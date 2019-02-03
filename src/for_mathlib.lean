/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import data.pfun category.functor category.applicative data.list.sort data.list.basic

universes u v

lemma eq_mp_heq :
  ∀ {α β : Sort*} {a : α} {a' : β} (h₂ : a == a'), (eq.mp (type_eq_of_heq h₂) a) = a'
| α ._ a a' heq.rfl := rfl

namespace sigma
variables {α₁ α₂ α₃ : Type u}
variables {β₁ : α₁ → Type v} {β₂ : α₂ → Type v} {β₃ : α₃ → Type v}
variables {g : sigma β₂ → sigma β₃} {f : sigma β₁ → sigma β₂}

theorem eq_fst {s₁ s₂ : sigma β₁} : s₁ = s₂ → s₁.1 = s₂.1 :=
by cases s₁; cases s₂; cc

theorem eq_snd {s₁ s₂ : sigma β₁} : s₁ = s₂ → s₁.2 == s₂.2 :=
by cases s₁; cases s₂; cc

@[extensionality]
lemma ext {x₀ x₁ : sigma β₁}
  (h₀ : x₀.1 = x₁.1)
  (h₁ : x₀.1 = x₁.1 → x₀.2 == x₁.2) :
  x₀ = x₁ :=
by casesm* sigma _; cases h₀; cases h₁ h₀; refl

lemma eta (x : sigma β₁) : sigma.mk x.1 x.2 = x :=
by cases x; refl

end sigma

namespace list

def zip_with₃ {α β γ φ} (f : α → β → γ → φ) : list α → list β → list γ → list φ
| (x::xs) (y::ys) (z::zs) := f x y z :: zip_with₃ xs ys zs
| _ _ _ := []

def mzip_with₃ {m : Type u → Type v} [applicative m] {α β γ φ} (f : α → β → γ → m φ) : list α → list β → list γ → m (list φ)
| (x::xs) (y::ys) (z::zs) := (::) <$> f x y z <*> mzip_with₃ xs ys zs
| _ _ _ := pure []

def mzip_with₄ {m : Type u → Type v} [applicative m] {α β γ φ ψ} (f : α → β → γ → φ → m ψ) :
  list α → list β → list γ → list φ → m (list ψ)
| (w :: ws) (x::xs) (y::ys) (z::zs) := (::) <$> f w x y z <*> mzip_with₄ ws xs ys zs
| _ _ _ _ := pure []

end list
namespace roption
variables {α : Type*} {β : Type*} {γ : Type*}

open function
lemma assert_if_neg {p : Prop}
  (x : p → roption α)
  (h : ¬ p)
: assert p x = roption.none :=
by { dsimp [assert,roption.none],
     have : (∃ (h : p), (x h).dom) ↔ false,
     { split ; intros h' ; repeat { cases h' with h' },
       exact h h' },
     congr,
     repeat { rw this <|> apply hfunext },
     intros h h', cases h', }

lemma assert_if_pos {p : Prop}
  (x : p → roption α)
  (h : p)
: assert p x = x h :=
by { dsimp [assert],
     have : (∃ (h : p), (x h).dom) ↔ (x h).dom,
     { split ; intros h'
       ; cases h' <|> split
       ; assumption, },
     cases hx : x h, congr, rw [this,hx],
     apply hfunext, rw [this,hx],
     intros, simp [hx] }

@[simp]
lemma roption.none_bind {α β : Type*} (f : α → roption β)
: roption.none >>= f = roption.none :=
by simp [roption.none,has_bind.bind,roption.bind,assert_if_neg]

end roption

namespace monad

@[simp]
lemma bind_pure_star {m} [monad m] [is_lawful_monad m] (x : m punit) :
  x >>= (λ (_x : punit), pure punit.star : punit → m punit) = x :=
by { transitivity,
     { apply congr_arg, ext z, cases z, refl },
     { simp } }

variables {α β γ : Type u}
variables {m : Type u → Type v} [monad m]

@[reducible]
def pipe (a : α → m β) (b : β → m γ) : α → m γ :=
λ x, a x >>= b

infixr ` >=> `:55 := pipe

@[functor_norm]
lemma map_bind_eq_bind_comp {α β γ} {m} [monad m] [is_lawful_monad m]
  (f : α → β) (cmd : m α) (g : β → m γ) :
  (f <$> cmd) >>= g = cmd >>= g ∘ f :=
by rw [← bind_pure_comp_eq_map,bind_assoc,(∘)]; simp

@[functor_norm]
lemma bind_map {α β γ} {m} [monad m] [is_lawful_monad m]
  (f : α → γ → β) (cmd : m α) (g : α → m γ) :
  cmd >>= (λ x, f x <$> g x) = do { x ← cmd, y ← g x, pure $ f x y }  :=
by congr; ext; rw [← bind_pure (g x),map_bind]; simp

@[functor_norm]
lemma bind_seq {α β γ : Type u} {m} [monad m] [is_lawful_monad m]
  (f : α → m (γ → β)) (cmd : m α) (g : α → m γ) :
  cmd >>= (λ x, f x <*> g x) = do { x ← cmd, h ← f x, y ← g x, pure $ h y }  :=
by congr; ext; simp [seq_eq_bind_map] with functor_norm

end monad

attribute [functor_norm] bind_assoc has_bind.and_then map_bind seq_left_eq seq_right_eq

namespace sum

variables {e : Type v} {α β : Type u}

protected def seq : Π (x : sum e (α → β)) (f : sum e α), sum e β
| (sum.inl e) _ := sum.inl e
| (sum.inr f) x := f <$> x

instance : applicative (sum e) :=
{ seq := @sum.seq e,
  pure := @sum.inr e }

instance : is_lawful_applicative (sum e) :=
by constructor; intros;
   casesm* _ ⊕ _; simp [(<*>),sum.seq,pure,(<$>)];
   refl

end sum

namespace functor
def foldl (α : Type u) (β : Type v) := α → α
def foldr (α : Type u) (β : Type v) := α → α

instance foldr.applicative {α} : applicative (foldr α) :=
{ pure := λ _ _, id,
  seq := λ _ _ f x, f ∘ x }

instance foldl.applicative {α} : applicative (foldl α) :=
{ pure := λ _ _, id,
  seq := λ _ _ f x, x ∘ f }

instance foldr.is_lawful_applicative {α} : is_lawful_applicative (foldr α) :=
by refine { .. }; intros; refl

instance foldl.is_lawful_applicative {α} : is_lawful_applicative (foldl α) :=
by refine { .. }; intros; refl

def foldr.eval {α β} (x : foldr α β) : α → α := x

def foldl.eval {α β} (x : foldl α β) : α → α := x

def foldl.cons {α β} (x : α) : foldl (list α) β :=
list.cons x

def foldr.cons {α β} (x : α) : foldr (list α) β :=
list.cons x

def foldl.cons' {α} (x : α) : foldl (list α) punit :=
list.cons x

def foldl.lift {α} (x : α → α) : foldl α punit := x
def foldr.lift {α} (x : α → α) : foldr α punit := x

end functor

instance {α : Type u} : traversable (prod.{u u} α) :=
{ map := λ β γ f (x : α × β), prod.mk x.1 $ f x.2,
  traverse := λ m _ β γ f (x : α × β), by exactI prod.mk x.1 <$> f x.2 }

namespace traversable

variables {t : Type u → Type u} [traversable t]

def to_list {α} (x : t α) : list α :=
@functor.foldr.eval _ (t punit) (traverse functor.foldr.cons x) []

end traversable

/-
namespace name

-- def append_suffix : name → string → name
-- | (mk_string s n) s' := mk_string (s ++ s') n
-- | n _ := n

end name
-/

namespace level

meta def fold_mvar {α} : level → (name → α → α) → α → α
| zero f := id
| (succ a) f := fold_mvar a f
| (param a) f := id
| (mvar a) f := f a
| (max a b) f := fold_mvar a f ∘ fold_mvar b f
| (imax a b) f := fold_mvar a f ∘ fold_mvar b f

meta def pred : level → level
| level.zero := level.zero
| (level.succ a) := a
| (level.max a b) := max (pred a) (pred b)
| (level.imax a b) := max (pred a) (pred b)
| l@(level.param a) := l
| l@(level.mvar a) := l


end level

namespace declaration

meta def univ_levels (d : declaration) : list level :=
d.univ_params.map level.param

end declaration

namespace native
namespace rb_map

-- #check rb_map

variables {key : Type} {val val' : Type}

-- section

variables [has_lt key] [decidable_rel ((<) : key → key → Prop)]
variables (f : val → val → val)

-- def intersect' : list (key × val) → list (key × val) → list (key × val)
-- | [] m := []
-- | ((k,x)::xs) [] := []
-- | ((k,x)::xs) ((k',x')::xs') :=
-- if h : k < k' then intersect' xs ((k',x')::xs')
-- else if k' < k then intersect' ((k,x)::xs) xs'
-- else (k,f x x') :: intersect' xs xs'

open function (on_fun)
def sort {α : Type} (f : α → key) : list α → list α := list.merge_sort (on_fun (<) f)

-- end

meta def filter_map (f : key → val → option val') (x : rb_map key val) : rb_map key val' :=
fold x (mk _ _) $ λa b m', (insert m' a <$> f a b).get_or_else m'

meta def intersect_with (m m' : rb_map key val) : rb_map key val :=
m.filter_map $ λ k x, f x <$> m'.find k

meta def intersect (x y : rb_map key val) : rb_map key val :=
intersect_with (function.const val) x y

meta def difference (m m' : rb_map key val) : rb_map key val :=
m.filter_map (λ k x, guard (¬ m'.contains k) >> pure x)

end rb_map
end native

namespace expr

meta def replace_all (e : expr) (p : expr → Prop) [decidable_pred p] (r : expr) : expr :=
e.replace $ λ e i, guard (p e) >> pure (r.lift_vars 0 i)

meta def const_params : expr → list level
| (const _ ls) := ls
| _ := []

meta def sort_univ : expr → level
| (sort ls) := ls
| _ := level.zero

meta def collect_meta_univ (e : expr) : list name :=
native.rb_set.to_list $ e.fold native.mk_rb_set $ λ e' i s,
match e' with
| (sort u) := u.fold_mvar (flip native.rb_set.insert) s
| (const _ ls) := ls.foldl (λ s' l, l.fold_mvar (flip native.rb_set.insert) s') s
| _ := s
end

meta def instantiate_pi : expr → list expr → expr
| (expr.pi n bi d b) (e::es) := instantiate_pi (b.instantiate_var e) es
| e _ := e

end expr

namespace tactic

meta def unify_univ (u u' : level) : tactic unit :=
unify (expr.sort u) (expr.sort u')

meta def add_decl' (d : declaration) : tactic expr :=
do add_decl d,
   pure $ expr.const d.to_name $ d.univ_params.map level.param

meta def renew : expr → tactic expr
| (expr.local_const uniq pp bi t) := mk_local' pp bi t
| e := fail format!"{e} is not a local constant"

meta def trace_error {α} (tac : tactic α) : tactic α :=
λ s, match tac s with
     | r@(result.success _ _) := r
     | (result.exception (some msg) pos s') := (trace (msg ()) >> result.exception (some msg) pos) s'
     | (result.exception none pos s') := (trace "no msg" >> result.exception none pos) s'
     end

meta def is_type (e : expr) : tactic bool :=
do (expr.sort _) ← infer_type e | pure ff,
   pure tt

meta def list_macros : expr → list (name × list expr) | e :=
e.fold [] (λ m i s,
  match m with
  | (expr.macro m args) := (expr.macro_def_name m, args) :: s
  | _ := s end)

meta def expand_untrusted (tac : tactic unit) : tactic unit :=
do tgt ← target,
   mv  ← mk_meta_var tgt,
   gs ← get_goals,
   set_goals [mv],
   tac,
   env ← get_env,
   pr ← env.unfold_untrusted_macros <$> instantiate_mvars mv,
   set_goals gs,
   exact pr

meta def binders : expr → tactic (list expr)
| (expr.pi n bi d b) :=
  do v ← mk_local' n bi d,
     (::) v <$> binders (b.instantiate_var v)
| _ := pure []

meta def rec_args_count (t c : name) : tactic ℕ :=
do ct ← mk_const c >>= infer_type,
   (list.length ∘ list.filter (λ v : expr, v.local_type.is_app_of t)) <$> binders ct

meta def match_induct_hyp (n : name) : list expr → list expr → tactic (list $ expr × option expr)
| [] [] := pure []
| [] _ := fail "wrong number of inductive hypotheses"
| (x :: xs) [] := (::) (x,none) <$> match_induct_hyp xs []
| (x :: xs) (h :: hs) :=
do t ← infer_type x,
   if t.is_app_of n
     then (::) (x,h) <$> match_induct_hyp xs hs
     else (::) (x,none) <$> match_induct_hyp xs (h :: hs)

meta def is_recursive_type (n : name) : tactic bool :=
do e ← get_env,
   let cs := e.constructors_of n,
   rs ← cs.mmap (rec_args_count n),
   pure $ rs.any (λ r, r > 0)

meta def better_induction (e : expr) : tactic $ list (name × list (expr × option expr) × list (name × expr)) :=
do t ← infer_type e,
   let tn := t.get_app_fn.const_name,
   env ← get_env,
   focus1 $
   do vs ← induction e,
      gs ← get_goals,
      vs' ← list.mzip_with₃ (λ n g (pat : name × list expr × list (name × expr)),
        do let ⟨_,args,σ⟩ := pat,
           set_goals [g],
           nrec ← rec_args_count tn n,
           let ⟨args,rec⟩ := args.split_at (args.length - nrec),
           args ← match_induct_hyp tn args rec,
           pure ((n,args,σ))) (env.constructors_of tn) gs vs,
      set_goals gs,
      pure vs'

meta def extract_def' {α} (n : name) (trusted : bool) (elab_def : tactic α) : tactic α :=
do cxt ← list.map to_implicit <$> local_context,
   t ← target,
   (r,d) ← solve_aux t elab_def,
   d ← instantiate_mvars d,
   t' ← pis cxt t,
   d' ← lambdas cxt d,
   let univ := t'.collect_univ_params,
   add_decl $ declaration.defn n univ t' d' (reducibility_hints.regular 1 tt) trusted,
   r <$ (applyc n; assumption)

open expr list nat

meta def remove_intl_const : expr → tactic expr
| v@(local_const uniq pp bi _) :=
  do t ← infer_type v,
     pure $ local_const uniq pp bi t
| e := pure e

meta def intron' : ℕ → tactic (list expr)
| 0 := pure []
| (succ n) := (::) <$> intro1 <*> intron' n

meta def unpi : expr → tactic (list expr × expr)
| (pi n bi d b) :=
  do v ← mk_local' n bi d,
     prod.map (cons v) id <$> unpi (b.instantiate_var v)
| e := pure ([],e)

meta def unify_app_aux : expr → expr → list expr → tactic expr
| e (pi _ _ d b) (a :: as) :=
do t ← infer_type a,
   unify t d,
   e' ← head_beta (e a),
   b' ← whnf (b.instantiate_var a),
   unify_app_aux e' b' as
| e t (_ :: _) := fail "too many arguments"
| e _ [] := pure e

meta def unify_app (e : expr) (args : list expr) : tactic expr :=
do t ← infer_type e >>= whnf,
   unify_app_aux e t args

meta def mk_has_repr : tactic unit :=
do `(has_repr %%t) ← target,
   let n := t.get_app_fn.const_name,
   d ← get_decl n,
   let r : reducibility_hints := reducibility_hints.regular 1 tt,
   env ← get_env,
   ls ← local_context,
   sig ← to_expr ``(%%t → string),
   (_,df) ← solve_aux sig $ do
     { match env.structure_fields n with
       | (some fs) :=
       do a ← intro1,
          [(_,xs,_)] ← cases_core a,
          let l := xs.length,
          out ← list.mzip_with₄ (λ x (fn : name) (y : expr) z,
            do let fn := (fn.update_prefix name.anonymous).to_string,
               to_expr ``(%%(reflect x) ++ %%(reflect fn) ++ " := " ++ repr %%y ++ %%(reflect z)))
            ("{ " :: list.repeat "  " (l-1)) fs xs (list.repeat ",\n" (l-1) ++ [" }"]),
          out.mfoldr (λ e acc : expr, to_expr ``(%%e ++ %%acc)) (reflect "" : expr) >>= exact,
          pure ()
       | none :=
       do g ← main_goal,
          a ← intro1,
          xs ← cases_core a,
          out ← xs.mmap $ λ ⟨c,xs,_⟩,
            do { out ← xs.mmap $ λ x, to_expr ``(" (" ++ repr %%x ++ ")"),
                 let c := (c.update_prefix name.anonymous).to_string,
                 out.mfoldl (λ acc e : expr, to_expr ``(%%acc ++ %%e)) (reflect c : expr) >>= exact },
          pure () end },
   df ← instantiate_mvars df >>= lambdas ls,
   t ← infer_type df,
   e ← add_decl' $ declaration.defn (n <.> "repr") d.univ_params t df r d.is_trusted,
   refine ``( { repr := %%(e.mk_app ls) } ),
   pure ()

@[derive_handler]
meta def has_repr_derive_handler : derive_handler :=
instance_derive_handler ``has_repr mk_has_repr

instance name.has_repr : has_repr name :=
{ repr := λ x, "`" ++ x.to_string }

private meta def report_invalid_simp_lemma {α : Type} (n : name): tactic α :=
fail format!"invalid simplification lemma '{n}' (use command 'set_option trace.simp_lemmas true' for more details)"

private meta def check_no_overload (p : pexpr) : tactic unit :=
when p.is_choice_macro $
  match p with
  | macro _ ps :=
    fail $ to_fmt "ambiguous overload, possible interpretations" ++
           format.join (ps.map (λ p, (to_fmt p).indent 4))
  | _ := failed
  end

private meta def add_simps : simp_lemmas → list name → tactic simp_lemmas
| s []      := return s
| s (n::ns) := do s' ← s.add_simp n, add_simps s' ns

private meta def simp_lemmas.resolve_and_add (s : simp_lemmas) (u : list name) (n : name) (ref : pexpr) : tactic (simp_lemmas × list name) :=
do
  p ← resolve_name n,
  check_no_overload p,
  -- unpack local refs
  let e := p.erase_annotations.get_app_fn.erase_annotations,
  match e with
  | const n _           :=
    (do b ← is_valid_simp_lemma_cnst n, guard b, save_const_type_info n ref, s ← s.add_simp n, return (s, u))
    <|>
    (do eqns ← get_eqn_lemmas_for tt n, guard (eqns.length > 0), save_const_type_info n ref, s ← add_simps s eqns, return (s, u))
    <|>
    (do env ← get_env, guard (env.is_projection n).is_some, return (s, n::u))
    <|>
    report_invalid_simp_lemma n
  | _ :=
    (do e ← i_to_expr_no_subgoals p, b ← is_valid_simp_lemma e, guard b, try (save_type_info e ref), s ← s.add e, return (s, u))
    <|>
    report_invalid_simp_lemma n
  end

meta def simp_lemmas.add_pexpr (s : simp_lemmas) (u : list name) (p : pexpr) : tactic (simp_lemmas × list name) :=
match p with
| (const c [])          := simp_lemmas.resolve_and_add s u c p
| (local_const c _ _ _) := simp_lemmas.resolve_and_add s u c p
| _                     := do new_e ← i_to_expr_no_subgoals p, s ← s.add new_e, return (s, u)
end

meta def simp_lemmas.append_pexprs : simp_lemmas → list name → list pexpr → tactic (simp_lemmas × list name)
| s u []      := return (s, u)
| s u (l::ls) := do (s, u) ← simp_lemmas.add_pexpr s u l, simp_lemmas.append_pexprs s u ls


meta def simp_only (ls : list pexpr) : tactic unit :=
do let ls := ls.map (simp_arg_type.expr), -- >>= simp_lemmas.append_pexprs simp_lemmas.mk [],
   -- interactive.dsimp tt ls [] (interactive.loc.ns [none])
   interactive.simp none tt ls [] (interactive.loc.ns [none])

open interactive.types interactive lean.parser

@[user_command]
meta def test_signature_cmd (_ : parse $ tk "#test") : lean.parser unit :=
do e ← ident,
show tactic unit, from
do d ← get_decl e,
   let e := @const tt d.to_name d.univ_levels,
   t ← infer_type e >>= pp,
   e.collect_meta_univ.enum.mmap' $ λ ⟨i,v⟩, unify_univ (level.mvar v) (level.param ("u_" ++ to_string i : string)),
   e ← instantiate_mvars e,
   e ← pp e,
   trace format!"\nexample : {t} :=\n{e}\n",
   pure ()

end tactic

namespace tactic.interactive

open lean lean.parser interactive interactive.types tactic

local postfix `*`:9000 := many

meta def clear_except (xs : parse ident *) : tactic unit :=
do let ns := name_set.of_list xs,
   local_context >>= mmap' (λ h : expr,
     when (¬ ns.contains h.local_pp_name) $
       try $ tactic.clear h) ∘ list.reverse

meta def splita := split; [skip, assumption]

@[hole_command]
meta def whnf_type_hole : hole_command :=
{ name := "Reduce expected type",
  descr := "Reduce expected type",
  action := λ es,
    do t ← match es with
           | [h] := to_expr h >>= infer_type >>= whnf
           | [] := target >>= whnf
           | _ := fail "too many expressions"
           end,
       trace t,
       pure [] }

meta def trace_error {α} (tac : tactic α) : tactic α
| s :=
match tac s with
| r@(interaction_monad.result.success a a_1) := r
| r@(interaction_monad.result.exception none a_1 a_2) := (trace "(no error message)" >> interaction_monad.result.exception none a_1) s
| r@(interaction_monad.result.exception (some msg) a_1 a_2) := (trace (msg ()) >> interaction_monad.result.exception none a_1) s
end


end tactic.interactive

instance subsingleton.fin0 {α} : subsingleton (fin 0 → α) :=
subsingleton.intro $ λ a b, funext $ λ i, fin.elim0 i

attribute [extensionality] function.hfunext

meta def options.list_names (o : options) : list name := o.fold [] (::)

meta def format.intercalate (fm : format) (xs : list format) : format :=
format.join $ list.intersperse fm xs

namespace expr

meta def bracket (p : ℕ) (fmt : format) (p' : ℕ) : format :=
if p' < p then format.paren fmt else fmt

meta def fmt_binder (n : name) : binder_info → format → format
| binder_info.default t := format!"({n} : {t})"
| binder_info.implicit t := format!"{{{n} : {t}}"
| binder_info.strict_implicit t := format!"⦃{n} : {t}⦄"
| binder_info.inst_implicit t := format!"[{n} : {t}]"
| binder_info.aux_decl t := "_"

meta def parsable_printer' : expr → list name → ℕ → format
| (expr.var a) l := λ _, format!"@{(l.nth a).get_or_else name.anonymous}"
| (expr.sort level.zero) l := λ _, to_fmt "Prop"
| (expr.sort (level.succ u)) l := λ _, format!"Type.{{{u}}"
| (expr.sort u) l := λ _, format!"Sort.{{{u}}"
| (expr.const a []) l := λ _, format!"@{a}"
| (expr.const a ls) l := λ _, format!"@{a}.{{{format.intercalate  \" \" $ list.map to_fmt ls}}"
| (expr.mvar a a_1 a_2) l := λ _, to_fmt a
| (expr.local_const a a_1 a_2 a_3) l := λ _, to_fmt a_1
| (expr.app a a_1) l := bracket 10 $ format!"{parsable_printer' a l 10} {parsable_printer' a_1 l 9}"
| (expr.lam a a_1 a_2 a_3) l := bracket 8 $ format!"λ {fmt_binder a a_1 $ parsable_printer' a_2 l 10}, {parsable_printer' a_3 (a :: l) 10}"
| (expr.pi a a_1 a_2 a_3) l :=
       if a_3.has_var_idx 0
          then bracket 8 $ format!"Π {fmt_binder a a_1 $ parsable_printer' a_2 l 10}, {parsable_printer' a_3 (a :: l) 10}"
          else bracket 8 $ format!"{parsable_printer' a_2 l 7} → {parsable_printer' a_3 (a :: l) 7}"
| (expr.elet a a_1 a_2 a_3) l := bracket 8 $ format!"let {a} : {parsable_printer' a_1 l 10} := {parsable_printer' a_2 l 10} in {parsable_printer' a_3 (a :: l) 10}"
| (expr.macro a a_1) l := λ _, to_fmt "unsupported"

meta def parsable_printer (e : expr) : format := parsable_printer' e [] 10

meta def as_binder (e : expr) := fmt_binder e.local_pp_name e.binding_info (parsable_printer e.local_type)

end expr
