
import .equations

namespace tactic

namespace parser

open interactive.types expr lean.parser

meta def var_decl (bi : binder_info) : lean.parser (list pexpr) :=
do n  ← ident,
   ns ← many ident,
   t ← tk ":" *> texpr <|> to_pexpr <$> pure ``(_),
   pure $ (n::ns : list _).map $ λ n, local_const n n bi t

meta def inst_decl : lean.parser (list pexpr) :=
do ns ← do
   { n  ← ident,
     ns ← many ident,
     tk ":",
     pure (n :: ns : list _) } <|> pure [`_],
   t ← texpr,
   pure $ ns.map $ λ n, local_const n n binder_info.inst_implicit t

-- meta def with_ctx {α} (vs : list expr) (tac : tactic α) : tactic α :=
-- do g ← pis vs `(true) >>= mk_meta_var,
--    set_goals [g],
--    intron vs.length,
--    tac

-- meta def add_local (n : name) (bi : binder_info) (t : option pexpr) : lean.parser unit :=
-- do parser.add_local (mk_local n)
-- do e ← parser.get_env,
--    e' ← parser.returnex $ e.add $ mk_definition n [] `(true) `(trivial),
--    parser.set_env e'

-- meta def

meta def var_decl' : list pexpr → lean.parser (list pexpr)
| vs :=
do  do
   { ns ← brackets "(" ")" (var_decl binder_info.default) <|>
       brackets "{" "}" (var_decl binder_info.implicit) <|>
       brackets "⦃" "⦄" (var_decl binder_info.strict_implicit) <|>
       brackets "[" "]" inst_decl,
     ns.mmap' lean.parser.add_local,
     var_decl' $ vs ++ ns
      } <|> pure vs
   -- pure vs.join
meta def collect_local_consts (es : list (pexpr)) : list (pexpr) :=
es.foldl (λ es (e : pexpr),
e.fold es (λ e' _ es, if e'.is_local_constant' then e' :: es else es)
) []

meta def parse_eqn : lean.parser (list pexpr × pexpr) :=
with_local_scope $
do pats ← many (lean.parser.pexpr std.prec.max tt),
   tk ":=",
   let vs := collect_local_consts pats,
   vs.mmap' add_local,
   rhs ← texpr,
   pure (pats, rhs)

meta def parse_body : lean.parser (pexpr ⊕ list (list pexpr × pexpr) ) :=
(tk ":=" *> sum.inl <$> texpr) <|>
sum.inr <$> many (tk "|" *> parse_eqn)

end parser
open expr
meta def local_binding_info' {elab} : expr elab → binder_info
| (expr.local_const _ _ bi _) := bi
| _ := binder_info.default

meta def add_local (v : pexpr) : tactic expr :=
do t ← to_expr (local_type v),
   v ← mk_local' (local_pp_name v) (local_binding_info' v) t,
   g ← mk_meta_var $ expr.pis [v] `(true),
   set_goals [g],
   intro (local_pp_name v)

meta def mk_sigma_val (u : level) : list expr → tactic (expr × expr)
| [] := pure (const ``punit [u],const ``punit.star [u])
| [v] := prod.mk <$> infer_type v <*> pure v
| (v :: vs) :=
  do (ts',vs') ← mk_sigma_val vs,
     t ← infer_type v,
     ts' ← lambdas [v] ts',
     x ← mk_mapp ``psigma [t,ts'],
     y ← mk_mapp ``psigma.mk [t,ts',v],
     pure (x,y vs')

-- lemma split_sigma {α} {β : α → Sort*} {γ} (h : ∀ x, β x → γ) : psigma β → γ
-- | ⟨x,y⟩ := h x y

-- #check function.const

meta def uncurry_sigma (u : level) : list expr → expr → tactic expr
| [] e := mk_app ``function.const [const ``punit [u]]
| [t] e := pure e
| (v::vs) e :=
  do e' ← head_beta (e v) >>= uncurry_sigma vs,
     mk_app ``psigma.uncurry [e'] >>= lambdas [v]

meta def curry_sigma (u : level) : list expr → expr → tactic expr
| [] e := pure (e $ const ``punit.star [u])
| [t] e := pure e
| (v::vs) e :=
  do e' ← mk_mapp ``psigma.curry [none,none,none,e],
     head_beta (e' v) >>= curry_sigma vs >>= lambdas [v]

meta def intro_sigma : list expr → tactic (list expr)
| [] := [] <$ intro1
| [x] := list.ret <$> intro x.local_pp_name
| (x :: xs) :=
  do refine ``(psigma.uncurry _),
     x ← intro x.local_pp_name,
     xs ← intro_sigma xs,
     pure $ x :: xs

meta def ctor_name {elab} : expr elab → string
| (var a) := "var"
| (sort a) := "sort"
| (const a a_1) := "const: " ++ to_string a
| (mvar unique pretty type) := "mvar"
| (local_const unique pretty bi type) := "local_const"
| (app a a_1) := "app"
| (lam var_name bi var_type body) := "lam"
| (pi var_name bi var_type body) := "pi"
| (elet var_name type assignment body) := "elet"
| (macro a a_1) := "macro"

meta def map_head {elab} (f : expr elab → expr elab) : expr elab → expr elab
| (pi n bi d b) := pi n bi d (map_head b)
| e := f e

meta def map_fn {elab} (f : expr elab → expr elab) : expr elab → expr elab
| (app fn x) := app (map_fn fn) x
| x := f x

meta def elab_shape (nn : name) (tc : list name) (n : name) (vs : list pexpr) (t : pexpr)
  (bod : pexpr ⊕ list (list pexpr × pexpr)) : tactic (list declaration) :=
do let n_shape' := n <.> "shape'",
   let sig' := local_const n_shape' n_shape' binder_info.default t,
   let sig_rec' := local_const n n binder_info.default t,
   eqns ← retrieve $ do
   { add_defn_equations [] (vs ++ [sig_rec']) sig' bod ff,
     get_eqn_lemmas_for ff ff n_shape' >>= mmap get_decl },
   let X : pexpr := local_const `X `X binder_info.default ``(_),
   let n_shape := n <.> "shape",
   let t₀ := map_head (λ _, X) t,
   let t₁ := map_head (λ x, app (map_fn (λ a, const (const_name a <.> "shape") []) x) X) t,
   let sig := local_const n_shape n_shape binder_info.default t₁,
   let sig_rec := local_const n n binder_info.default t₀,
   let f (e : pexpr) : pexpr := e.replace $ λ e' _,
     if e'.is_constant ∧ e'.const_name.get_prefix = nn ∧ e'.const_name ∈ tc
       then
         let n' := e'.const_name.update_prefix (e'.const_name.get_prefix <.> "shape") in
         some $ const n' []
       else none,
   let bod := sum.map f (list.map $ prod.map id f) bod,
   add_defn_equations [] (vs ++ [X,sig_rec]) sig bod ff,
   pure eqns

-- | universe polymorphism
meta def elab_corec (n : name) (vs args : list expr) (t' : expr) : tactic unit :=
do let tn := t'.get_app_fn.const_name,
   corec_t ← mk_mapp (tn <.> "corec₁") $ t'.get_app_args.map some,
   (pi _ _ (sort u) _) ← infer_type corec_t,
   (state,arg) ← mk_sigma_val u args,
   infer_type state >>= unify (sort u),
   let corec_t := corec_t state,
   `(%%shape_t → _) ← infer_type corec_t,
   shape_fn ← mk_mapp (n <.> "shape") (vs.map some),
   (_,shape) ← solve_aux shape_t $ do
   { [X, exit_fn, rec_fn] ← intron' 3,
     xs ← intro_sigma args,
     rec_fn' ← curry_sigma u xs rec_fn,
     exact $ (shape_fn X rec_fn').mk_app xs },
   shape ← instantiate_mvars shape,
   let corec_t := corec_t shape,
   t ← pis (vs ++ args) t' >>= instantiate_mvars,
   us ← t.collect_meta_univ.enum.mmap $ λ ⟨i,u⟩, do
   { let un := (`u).append_after i,
     unify_univ (level.param un) (level.mvar u),
     pure un },
   t ← instantiate_mvars t,
   df ← lambdas (vs ++ args) (corec_t arg) >>= instantiate_mvars,
   add_decl $ mk_definition n us t df

lemma mvqpf.cofix.ext_mk' {n : ℕ} {F : typevec (n + 1) → Type*} [_inst_1 : mvfunctor F] [q : mvqpf F] {α : typevec n}
  (x : F (α ::: mvqpf.cofix F α)) (y : mvqpf.cofix F α)
  (h : mvqpf.cofix.mk x = y) :
  x = mvqpf.cofix.dest y :=
mvqpf.cofix.ext_mk _ _ ((mvqpf.cofix.mk_dest y).symm ▸ h)

-- todo: test nesting guarded call in if-then-else
-- todo: use escape hatch (e.g. monad bind)
meta def elab_eqns (eqns : list declaration) (univs : list name) (tn n : name) (vs args : list expr) (t' : expr) : tactic unit :=
do shape_fn ← mk_mapp (n <.> "shape") (vs.map some),
   shape_t ← infer_type shape_fn,
   (X :: rec_fn :: xs, hd) ← mk_local_pis shape_t,
   d' ← get_decl n,
   let c' := (@const tt d'.to_name d'.univ_levels).mk_app vs,
   xs ← get_eqn_lemmas_for ff ff (n <.> "shape"),
   shape_def ← resolve_name (n <.> "shape"),
   (s₀ ,_) ← mk_simp_set tt []
         [simp_arg_type.expr  ``(psigma.curry),simp_arg_type.expr ``(psigma.uncurry)],

   (s,_) ← mk_simp_set tt [`typevec]
         [simp_arg_type.symm_expr ``(typevec.append_fun_id_id),
          simp_arg_type.expr ``(typevec.id_eq_nil_fun),
          simp_arg_type.expr  ``(psigma.curry),
          simp_arg_type.expr ``(psigma.uncurry),
          simp_arg_type.expr shape_def],

   mzip_with' (λ x (d : declaration), do
     (c,t) ← decl_mk_const d,
     t ← instantiate_unify_pi t (vs ++ [c']),
     (vs',t) ← mk_local_pis t,
     (lhs,rhs) ← match_eq t,
     let vars := lhs.get_app_args.drop $ vs.length+1,
     let lhs' := c'.mk_app vars,
     prop ← mk_app `eq [lhs',rhs],
     (_,pr) ← solve_aux prop $ do
     { delta_target [n,tn <.> "corec₁"],
       refine ``(mvqpf.cofix.ext _ _ _),
       mk_const ``mvqpf.cofix.dest_corec₁ >>= rewrite_target,
       dsimp_target s₀ [] { fail_if_unchanged := ff },
       mk_const x >>= rewrite_target,
       `(%%a = mvqpf.cofix.dest %%b) ← target,
       e ← mk_mapp ``mvqpf.cofix.ext_mk' [none,none,none,none,none,a,b],
       apply e, reflexivity,
       intros,
       dsimp_target s₀ [] { fail_if_unchanged := ff },
       mk_const x >>= rewrite_target,
       simp_target s [``mvfunctor.map],
       reflexivity },
     pr ← instantiate_mvars pr >>= lambdas (vs ++ vs') >>= instantiate_mvars,
     prop ← instantiate_mvars prop >>= pis (vs ++ vs') >>= instantiate_mvars,
     let eqn_n := (d.to_name.replace_prefix (n <.> "shape'") n),
     add_decl $ declaration.thm eqn_n d'.univ_params prop (pure pr),
     add_eqn_lemmas eqn_n
     ) xs eqns,
   pure ()

setup_tactic_parser

meta def elab_codef (n : name) (vs : list pexpr) (t : pexpr)
  (bod : pexpr ⊕ list (list pexpr × pexpr)) : tactic unit :=
do vs' ← vs.mmap add_local,
   t' ← to_expr t,
   (args,t') ← mk_local_pis t',

   let tn := t'.get_app_fn.const_name,
   spec ← get_type_spec tn,
   let cs := spec.ctors.map type_cnstr.name,
   let us := spec.u_names,
   eqns ← elab_shape tn cs n vs t bod,
   elab_corec n vs' args t',

   elab_eqns eqns us tn n vs' args t',
   pure ()

-- use cases_on of data types in built-in equation compiler
-- hook generated equation into the "real" equations
@[user_command]
meta def codef_decl (meta_info : decl_meta_info) (_ : parse (tk "codef")) : lean.parser unit :=
with_local_scope $
do n ← ident,
   vs ← parser.var_decl' [],
   tk ":",
   t ← texpr,
   parser.add_local $ local_const n n binder_info.default t,
   bod ← parser.parse_body,
   elab_codef n vs t bod

end tactic

-- codata str (α : Type)
-- | nil : str
-- | cons : α → str → str

-- -- codef map'' {α β} (f : α → β) : str α → str β
-- -- | str.nil := str.nil
-- -- | (str.cons x xs) := str.cons (f x) (map'' xs)

-- -- -- hole errors wrong place
-- -- -- compile pattern matching on codata
-- -- codef map {α β} (f : α → β) : str α → str β
-- -- | s := str.cases_on s str.nil (λ x xs, str.cons (f x) (map xs))

-- codef map' {α β} (f : α → β) : list α → str β
-- | [] := str.nil
-- | (x :: xs) := str.cons (f x) (map' xs)

-- #print prefix map'

-- -- | s := str.cases_on s str.nil (λ x xs, str.cons (f x) (map' xs))
-- .
-- -- weird behavior if `str.cons x $ enum_from x.succ`
-- codef enum_from : ℕ → str ℕ
-- | x := str.cons x (enum_from x.succ)

-- #exit

-- #exit

-- codata str (α : Type)
-- | nil : str
-- | cons : α → str → str
-- #print prefix str

-- set_option trace.simplify.rewrite_failure true
-- set_option trace.simplify true
-- set_option pp.implicit true
-- #check @typevec.id 0
-- codef map' {α β} (f : α → β) : list α → str β
-- | [] := str.nil
-- | (x :: xs) := str.cons (f x) (map' xs)


-- #print prefix map'

-- set_option trace.simplify.rewrite_failure true
-- set_option trace.simplify true

-- example {α β} (f : α → β) (x y : α) : map' f [x,y] = map' f [] :=
-- begin
--   -- rw [map',map'],
--   -- rw [map'.equations._eqn_1],
--  --  do { let args := [``(map'.equations._eqn_2),``(map'.equations._eqn_1)],
--  --       (s,_) ← tactic.simp_lemmas.append_pexprs simp_lemmas.mk [] args,
--  --       d ← tactic.get_decl ``map'.equations._eqn_2,
--  --       tactic.trace d.univ_params,
--  --       tactic.simp_target s [],
--  --       -- tactic.decode_simp_arg_list_with_symm args,
--  --       -- tactic.mk_simp_set_core tt [] args ff >>= tactic.trace,
--  --       -- (hs, gex, hex, all_hyps) ← tactic.decode_simp_arg_list_with_symm args,
--  --       -- tactic.trace hs,
--  --       -- tactic.trace gex,
--  --       -- tactic.trace hex,
--  --       -- hs ← tactic.get_eqn_lemmas_for ff ``map',
--  --       -- tactic.trace hs,
--  --       -- hs.mmap (tactic.mk_const >=> tactic.trace_expr),
--  --       pure ()
--  -- },

--   simp only [map'],
-- end


-- #exit
-- set_option trace.simp_lemmas true
-- codata part (α : Type)
-- | pure : α → part
-- | delay : part → part

-- -- #print part._ctors
-- -- set_option trace.app_builder true

-- -- codef diverge'' {α} : ℕ → list ℕ → ℤ → part α
-- -- | x xs k :=
-- -- part.delay  (diverge'' x.succ (x :: xs) k)

-- -- #print prefix   diverge''
-- -- set_option trace.auto.finish true
-- -- set_option trace.simp_lemmas.invalid true

-- codef diverge' {α} : part α :=
-- part.delay diverge'

-- -- #print prefix part.corec₁

-- -- #print prefix diverge'

-- -- def diverge {α} : part α :=
-- -- part.corec _ unit (λ _, part.shape.delay ()) ()

-- -- run_cmd do
-- -- t ← tactic.get_eqn_lemmas_for tt ff ``diverge',
-- -- tactic.trace t,
-- -- t ← tactic.interactive.get_rule_eqn_lemmas (tactic.interactive.rw_rule.mk ⟨0,0⟩ tt ``(diverge')),
-- -- tactic.trace t,
-- -- t ← tactic.interactive.get_rule_eqn_lemmas (tactic.interactive.rw_rule.mk ⟨0,0⟩ tt ``(diverge')),
-- -- tactic.trace t

-- -- example {α} (x : part α) : x = diverge :=
-- -- by rw diverge

-- -- example {α} (x : part α) : x = diverge' :=
-- -- by rw diverge'

-- -- example {α} (x : part α) : x = diverge' :=
-- -- by simp  [diverge']

-- -- example {α} (x : part α) : x = diverge' :=
-- -- by do
-- -- { t ← tactic.get_eqn_lemmas_for tt ff ``diverge',
-- --   t ← t.mmap tactic.mk_const,
-- --   t.mmap tactic.infer_type >>= tactic.trace,
-- --   tactic.trace_state,
-- --   t.mmap' tactic.rewrite_target }

-- -- #exit

-- codata str (α : Type)
-- | nil : str
-- | cons : α → str → str

-- -- -- hole errors wrong place
-- -- -- compile pattern matching on codata
-- -- codef map {α β} (f : α → β) : str α → str β
-- -- | s := str.cases_on s str.nil (λ x xs, str.cons (f x) (map xs))

-- codef map' {α β} (f : α → β) : list α → str β
-- | [] := str.nil
-- | (x :: xs) := str.cons (f x) (map' xs)

-- -- weird behavior if `str.cons x $ enum_from x.succ`
-- codef enum_from : ℕ → str ℕ
-- | x := str.cons x (enum_from x.succ)

-- -- #exit
-- -- #check part.bisim_rel

-- -- #check @mvqpf.cofix.bisim
-- -- #check part.shape.liftr
-- -- #print part.shape.liftr
-- -- #print prefix part.shape

-- section bisim
-- variables {α : Type}
-- variables (r : part α → part α → Prop)
-- variables (hh : ∀ (x y : part α),
--     r x y → part.shape.liftr eq r (mvqpf.cofix.dest x) (mvqpf.cofix.dest y))

-- -- generate me
-- lemma part.bisim
--   (x y : part α) (hr : r x y) : x = y :=
-- mvqpf.cofix.bisim₂ r (λ x y hr, (part.shape.liftr_iff _ _ _ _).2 $ hh _ _ hr) _ _ hr

-- end bisim

-- section part

-- -- generate me
-- lemma part.shape.dest_pure {α} (x : α) :
--   mvqpf.cofix.dest (part.pure x) = part.shape.pure x :=
-- mvqpf.cofix.dest_mk _

-- -- generate me
-- lemma part.shape.dest_delay {α} (x : part α) :
--   mvqpf.cofix.dest (part.delay x) = part.shape.delay x :=
-- mvqpf.cofix.dest_mk _

-- end part

-- section bisim
-- variables {α : Type}
-- variables (r : part α → part α → Prop)
-- variables
--   (hh₀₀ : ∀ (x y : α),
--     r (part.pure x) (part.pure y) → x = y)
--   (hh₀₁ : ∀ (x : α) (y : part α),
--     r (part.pure x) (part.delay y) → false)
--   (hh₁₀ : ∀ (x : part α) (y : α),
--     r (part.delay x) (part.pure y) → false)
--   (hh₁₁ : ∀ (x y : part α),
--     r (part.delay x) (part.delay y) → r x y)

-- include hh₀₀ hh₀₁ hh₁₀ hh₁₁

-- -- generate me
-- lemma part.bisim₂ :
--   ∀ (x y : part α), r x y → x = y :=
-- part.bisim _ $
-- begin
--   intros x y, apply part.cases_on y; apply part.cases_on x,
--   all_goals
--   { intros a b hab,
--     simp [part.shape.dest_pure,part.shape.dest_delay] },
--   { constructor, apply hh₀₀ _ _ hab },
--   { cases hh₁₀ _ _ hab },
--   { cases hh₀₁ _ _ hab },
--   { constructor, apply hh₁₁ _ _ hab },
-- end

-- end bisim

-- -- section corec

-- -- #check mvqpf.corecF
-- -- #check @part.corec

-- -- -- lemma part.corec_eq {α X : Type} (f : Π X, X → part.shape α X) (x₀ : X) :
-- -- --   part.corec _ _ (f X) x₀ = mvqpf.cofix.mk (f _ (part.corec _ _ (f X) x₀)) :=
-- -- -- begin
-- -- --   delta part.corec,
-- -- --   apply mvqpf.cofix.ext,
-- -- --   rw [mvqpf.cofix.dest_corec,mvqpf.cofix.dest_mk], dsimp, refl,
-- -- -- end

-- -- end corec

-- -- #print prefix mvqpf.cofix
-- -- #check @option.no_confusion
-- -- #check part.cases_on
-- -- #print prefix part
-- -- -- #exit
-- -- #print prefix part.shape.internal.map
-- -- #check mvfunctor.map

-- --| todo: generate this
-- -- example {α} : @diverge' α = part.delay diverge' :=
-- -- begin
-- --   apply mvqpf.cofix.ext,
-- --   rw [diverge,part.shape.dest_delay],
-- --   delta part.corec,
-- --   erw [mvqpf.cofix.dest_corec,← typevec.append_fun_id_id],
-- --   dsimp [mvfunctor.map],
-- --   convert part.shape.internal.map._equation_1 _ _ _,
-- --   ext i, cases i
-- -- end

-- -- #exit

-- -- example {α} : @diverge α = part.delay _ diverge :=
-- -- begin
-- --   -- conv { to_lhs, rw diverge, },
-- --   apply part.bisim₂ (λ x y, x = diverge ∧ y = part.delay _ diverge) _ _ _ _ _ _ ⟨rfl,rfl⟩;
-- --   dsimp;
-- --   rintro x y ⟨hx,hy⟩,
-- --   { have := @part.no_confusion _ (x=y) _ _ hy,
-- --     delta part.no_confusion_type at this,
-- --     rw [part.cases_on_pure,part.cases_on_delay] at this,
-- --     exact this, },
-- --   { have := @part.no_confusion _ false _ _ hx,
-- --     delta part.no_confusion_type at this,
-- --     rw [diverge,part.cases_on_pure,part.cases_on_delay] at this,
-- --     exact this, },
-- --  subst hx, subst hy,
-- -- end
-- -- #exit

-- -- codata str (α : Type)
-- -- | nil : str
-- -- | cons : α → str → str

-- -- #check str.shape.liftr_def
-- -- #check str.shape.liftr_iff

-- -- #check part.corec
-- -- #print prefix part
-- -- #print prefix mvqpf.cofix
-- -- #exit

-- -- def map {α β} (f : α → β) (x : str α) : str β :=
-- -- str.corec _ _
-- -- (λ x, @str.cases_on _ (λ _, str.shape β (str α)) x
-- --   str.shape.nil
-- --   (λ (x : α) (y : str α), str.shape.cons (f x) y))
-- -- x

-- -- -- todo: encapsulate data type in struct
-- -- lemma map_eqn_1 {α β} (f : α → β) (x : α) (xs : str α) :
-- --   map f (str.cons _ x xs) = str.cons _ (f x) (map f xs) :=
-- -- begin
-- --   dsimp [map],
-- --   apply mvqpf.cofix.ext,
-- --   erw [mvqpf.cofix.dest_corec,mvqpf.cofix.dest_mk],
-- --   dsimp, erw [str.cases_on_cons,← typevec.append_fun_id_id, typevec.eq_nil_fun typevec.id],
-- --   dsimp [(<$$>)],
-- --   erw [str.shape.internal.map._equation_1 id (mvqpf.cofix.corec _) _ _],
-- --   refl,
-- -- end

-- -- lemma map_eqn_2 {α β} (f : α → β) (x : α) (xs : str α) :
-- --   mvqpf.cofix.dest (map f (str.cons _ x xs)) = str.shape.cons (f x) (map f xs) :=
-- -- begin
-- --   rw [map], delta str.corec,
-- --   rw [mvqpf.cofix.dest_corec],
-- --   dsimp, rw str.cases_on_cons,
-- --   refl
-- -- end

-- -- def enum_from : ℕ → str ℕ :=
-- -- str.corec _ _ (λ x, str.shape.cons x x.succ)

-- lemma enum_from_eqn_1 (i : ℕ) : mvqpf.cofix.dest (enum_from i) = str.shape.cons i (enum_from i.succ) :=
-- begin
--   rw [enum_from], symmetry, delta str.cons,
--   rw [mvqpf.cofix.dest_mk], refl
-- end

-- -- lemma enum_from_eqn_2 (i : ℕ) : enum_from i = str.cons i (enum_from i.succ) :=
-- -- begin
-- --   rw [enum_from], symmetry, delta str.cons,
-- --   rw [mvqpf.cofix.dest_mk], refl
-- -- end

-- -- example {x y} : enum_from (x + y) = map (λ z, z + y) (enum_from x) :=
-- -- begin
-- --   bisim₂ x,
-- --   rw [Ha,Hb],
-- --   rw [typevec.rel_last',typevec.repeat_eq,typevec.drop,typevec.repeat_eq], -- typevec.split_fun,str.shape.liftr_iff],
-- --   erw [str.shape.liftr_iff,enum_from_eqn_1,enum_from_eqn_2 x],
-- --   simp [map_eqn_2],
-- --   constructor, refl,
-- --   refine ⟨x.succ,_,rfl⟩,
-- --   rw nat.succ_add,
-- -- end
