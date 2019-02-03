
import data.fix.inductive_decl
import mvqpf
import data.fix.equations

universes u

lemma foo {n} {p : mvpfunctor n} {v} (C : p.apply v → Sort*) {a : p.A} {f g : p.B a ⟹ v} (h : f = g) (x : C ⟨a,f⟩) : C ⟨a,g⟩ := sorry

namespace tactic

-- meta def coinductive_def (meta_info : decl_meta_info) (_ : parse $ tk "codata") : lean.parser unit :=
-- do decl ← inductive_decl.parse meta_info,
--    decl ← inductive_type.of_decl decl,
--    updateex_env $ λ e, pure $ e.add_namespace decl.name,
--    head_t  ← trace_error $ mk_head_t  decl,
--    child_t ← trace_error $ mk_child_t decl,
--    _       ← trace_error $ mk_branch_discr decl head_t child_t,
--    _       ← trace_error $ mk_pos_functor   decl,
--    _       ← trace_error $ mk_positive_inst decl,
--    _       ← trace_error $ mk_cofix  decl,
--    _       ← trace_error $ mk_constr decl,
--    _       ← trace_error $ mk_cases  decl,
--    _       ← trace_error $ mk_no_confusion_type decl,
--    _       ← trace_error $ mk_no_confusion decl,
--    _       ← trace_error $ mk_bisimulation_pred decl,
--    add_meta_definition (decl.name <.> "_info") [] `(inductive_type) (reflect decl),
--    coinduct_ctor.attr.set (decl.name <.> "_info") () tt,
--    pure ()

meta def mk_qpf_instance : tactic unit :=
do
   fail "fo"

open native

meta def map_arg' (m : rb_map expr expr) : expr → expr → tactic expr
| e (expr.pi n bi d b) :=
do v ← mk_local' n bi d,
   e' ← head_beta (e v) >>= whnf,
   map_arg' e' (b.instantiate_var v) >>= lambdas [v]
| e v@(expr.local_const _ _ _ _) :=
do some f ← pure $ m.find v | pure e,
   pure $ f e
| e _ := pure e

meta def map_arg (m : rb_map expr expr) (e : expr) : tactic expr :=
infer_type e >>= whnf >>= map_arg' m e

meta def find_dead_occ : rb_map expr ℕ → expr → rb_map expr ℕ
| m `(%%a → %%b) := find_dead_occ (a.list_local_consts.foldl rb_map.erase m) b
| m (expr.local_const _ _ _ _) := m
| m e := e.list_local_consts.foldl rb_map.erase m

meta def live_vars (n : name) (params : list expr) : tactic $ rb_map expr ℕ × rb_map expr ℕ :=
do let vs := rb_map.of_list $ params.enum.map prod.swap,
   env ← get_env,
   let ls := env.constructors_of n,
   ls ← ls.mmap $ λ c,
     do { c ← mk_const c,
          let x := c.mk_app params,
          (ps,_) ← infer_type x >>= mk_local_pis,
          ts ← ps.mmap infer_type,
          let r := ts.foldl find_dead_occ vs,
          pure $ ts.foldl find_dead_occ vs },
   let m := ls.foldl rb_map.intersect vs,
   m.mfilter $ λ e _, expr.is_sort <$> infer_type e,
   let m' := vs.difference m,
   pure (m,m')

meta instance : has_repr expr := ⟨ to_string ⟩
meta instance task.has_repr {α} [has_repr α] : has_repr (task α) := ⟨ repr ∘ task.get ⟩

open level
meta def level.repr : level → ℕ → string
| zero n := repr n
| (succ a) n := level.repr a n.succ
| (max x y) n := sformat!"(max {level.repr x n} {level.repr y n})"
| (imax x y) n := sformat!"(imax {level.repr x n} {level.repr y n})"
| (param a) n := if n = 0 then repr a
                          else sformat!"({n} + {repr a})"
| (mvar a) n := if n = 0 then repr a
                         else sformat!"({n} + {repr a})"

meta instance level.has_repr : has_repr level := ⟨ λ l, level.repr l 0 ⟩
-- | x := _

-- attribute [derive has_reflect] reducibility_hints declaration
attribute [derive has_repr] reducibility_hints declaration type_cnstr inductive_type

@[derive has_repr]
meta structure internal_mvfunctor :=
(decl : declaration)
(induct : inductive_type)
(def_name eqn_name map_name abs_name repr_name pfunctor_name : name)
(univ_params : list level)
(vec_lvl : level)
(live_params : list $ expr × ℕ)
(dead_params : list $ expr × ℕ)
(params : list expr)
(type : expr)

-- @[replaceable]
meta def mk_inductive' : inductive_type → lean.parser unit
| decl :=
do let n₀ := name.anonymous,
   t ← pis decl.idx decl.type,
   cn ← mk_local_def (decl.name.replace_prefix decl.pre n₀) t,
   brs ← decl.ctors.mmap $ λ c,
       do { let rt := cn.mk_app c.result,
            t ← pis c.args rt,
            pure format!"| {(c.name.update_prefix n₀).to_string} : {expr.parsable_printer t}" },
   args ← decl.params.mmap $ λ p,
     do { t ← infer_type p,
          pure $ expr.fmt_binder p.local_pp_name p.binding_info (expr.parsable_printer t) },
   let xs := format!"
inductive {cn} {format.intercalate \" \" args} : {expr.parsable_printer t}
{format.intercalate \"\n\" brs}",
   trace xs,
   lean.parser.with_input lean.parser.command_like xs.to_string,
   pure ()

meta def internalize_mvfunctor (ind : inductive_type) : tactic internal_mvfunctor :=
do let decl := declaration.cnst ind.name ind.u_names ind.type tt,
   let n := decl.to_name,
   let df_name := n <.> "internal",
   let lm_name := n <.> "internal_eq",
   -- decl ← get_decl n,
   (params,t) ← mk_local_pis decl.type,
   let params := ind.params ++ params,
   (m,m') ← live_vars n params,
   -- trace m, trace m',
   let m := rb_map.sort prod.snd m.to_list,
   let m' := rb_map.sort prod.snd m'.to_list,
   u ← mk_meta_univ,
   let vars := string.intercalate "," (m.map to_string),
   (params.mmap' (λ e, infer_type e >>= unify (expr.sort u))
     <|> fail format!"live type parameters ({params}) are not in the same universe" : tactic _),
   -- u' ← instantiate_mvars u,
   -- trace format!"univ: {u'}",
   (level.succ u) ← get_univ_assignment u <|> pure level.zero.succ,
   ts ← (params.mmap infer_type : tactic _),
   -- trace format!"univ: {ts}",
   pure { decl := decl,
          induct := ind,
          def_name := df_name,
          eqn_name := lm_name,
          map_name := (df_name <.> "map"),
          abs_name := (df_name <.> "abs"),
          repr_name := (df_name <.> "repr"),
          pfunctor_name := n <.> "pfunctor",
          vec_lvl := u,
          univ_params := decl.univ_params.map level.param,
          live_params := m,
          dead_params := m',
          params := params,
          type := t }

-- meta def internalize_mvfunctor (n : name) : tactic internal_mvfunctor :=
-- do let df_name := n <.> "internal",
--    let lm_name := n <.> "internal_eq",
--    decl ← get_decl n,
--    (params,t) ← mk_local_pis decl.type,
--    (m,m') ← live_vars n params,
--    let m := rb_map.sort prod.snd m.to_list,
--    let m' := rb_map.sort prod.snd m'.to_list,
--    u ← mk_meta_univ,
--    let vars := string.intercalate "," (m.map to_string),
--    params.mmap' (λ e, infer_type e >>= unify (expr.sort u)) <|> fail format!"live type parameters ({params}) are not in the same universe",
--    (level.succ u) ← get_univ_assignment u <|> pure level.zero.succ,
--    pure { decl := decl,
--           def_name := df_name,
--           eqn_name := lm_name,
--           map_name := (df_name <.> "map"),
--           pfunctor_name := n <.> "pfunctor",
--           vec_lvl := u,
--           univ_params := decl.univ_params.map level.param,
--           live_params := m,
--           dead_params := m',
--           params := params,
--           type := t }

notation `⦃ ` r:( foldr `, ` (h t, typevec.append1 t h) fin.elim0 ) ` ⦄` := r
notation `⦃`  `⦄` := fin.elim0

local prefix `♯`:0 := cast (by try { simp only with typevec }; congr' 1; try { simp only with typevec })

meta def mk_internal_functor_def (func : internal_mvfunctor) : tactic unit :=
do let trusted := func.decl.is_trusted,
   let arity := func.live_params.length,
   let vec := @expr.const tt ``_root_.typevec [func.vec_lvl] `(arity),
   v_arg ← mk_local_def `v_arg vec,
   t ← pis (func.dead_params.map prod.fst ++ [v_arg]) func.type,
   -- trace "a",
   (_,df) ← @solve_aux unit t $ do
     { m' ← func.dead_params.mmap $ λ v, prod.mk v.2 <$> intro v.1.local_pp_name,
       -- trace "- c",
       vs ← func.live_params.mmap $ λ x, do
         { refine ``(typevec.typevec_cases_cons _ _),
           x' ← intro x.1.local_pp_name,
           pure (x.2,x') },
       refine ``(typevec.typevec_cases_nil _),
       let args := (rb_map.sort prod.fst (m' ++ vs)).map prod.snd,
       let e := (@expr.const tt func.decl.to_name (func.decl.univ_params.map level.param)).mk_app args,
       -- trace_state,
       -- trace e,
       -- infer_type e >>= trace,
       -- trace "b",
       exact e },
   -- trace "a",
   df ← instantiate_mvars df,
   add_decl $ declaration.defn func.def_name func.decl.univ_params t df (reducibility_hints.regular 1 tt) trusted

meta def mk_live_vec (u : level) (vs : list expr) : tactic expr :=
do nil ← mk_mapp ``fin.elim0 [@expr.sort tt $ level.succ u],
   vs.mfoldr (λ e s, mk_mapp ``typevec.append1 [none,s,e]) nil

meta def mk_map_vec (u : level) (vs : list expr) : tactic expr :=
do let nil := @expr.const tt ``typevec.nil_fun [u,u],
   vs.mfoldr (λ e s,
     mk_mapp ``typevec.append_fun [none,none,none,none,none,s,e]) nil

meta def mk_internal_functor_app (func : internal_mvfunctor) : tactic expr :=
do let decl := func.decl,
   vec ← mk_live_vec func.vec_lvl $ func.live_params.map prod.fst,
   pure $ (@expr.const tt func.def_name decl.univ_levels).mk_app (func.dead_params.map prod.fst ++ [vec])

meta def mk_internal_functor_eqn (func : internal_mvfunctor) : tactic unit :=
do let decl := func.decl,
   lhs ← mk_internal_functor_app func,
   let rhs := (@expr.const tt decl.to_name decl.univ_levels).mk_app func.params,
   p ← mk_app `eq [lhs,rhs] >>= pis func.params,
   (_,pr) ← solve_aux p $ intros >> reflexivity,
   pr ← instantiate_mvars pr,
   -- trace "unknown u",
   add_decl $ declaration.thm func.eqn_name decl.univ_params p (pure pr)

-- meta def mk_internal_functor (n : name) : tactic internal_mvfunctor :=
-- do decl ← get_decl n,
--    func ← internalize_mvfunctor decl,
--    mk_internal_functor_def func,
--    mk_internal_functor_eqn func,
--    pure func

meta def mk_internal_functor' (d : interactive.inductive_decl) : lean.parser internal_mvfunctor :=
do d ← inductive_type.of_decl d,
   -- trace d.u_params,
   -- trace $ repr d,
   mk_inductive' d,
   func ← internalize_mvfunctor d,
   -- trace $ repr func,
   mk_internal_functor_def func,
   -- trace "foo",
   mk_internal_functor_eqn func,
   pure func

open typevec

meta def destruct_typevec (func : internal_mvfunctor) (v : name) : tactic (list $ expr × expr × expr × ℕ) :=
do vs ← func.live_params.mmap $ λ x : expr × ℕ, do
     { refine ``(typevec_cases_cons₃ _ _),
       α ← get_unused_name `α >>= intro,
       β ← get_unused_name `β >>= intro,
       f ← get_unused_name `f >>= intro,
       pure (α,β,f,x.2) },
   refine ``(typevec_cases_nil₃ _),
   pure vs

def mk_arg_list {α} (xs : list (α × ℕ)) : list α :=
(rb_map.sort prod.snd xs).map prod.fst

meta def internal_expr (func : internal_mvfunctor) :=
(@expr.const tt func.def_name func.decl.univ_levels).mk_app (func.dead_params.map prod.fst)

meta def functor_expr (func : internal_mvfunctor) :=
(@expr.const tt func.pfunctor_name func.decl.univ_levels).mk_app (func.dead_params.map prod.fst)

meta def mk_mvfunctor_map (func : internal_mvfunctor) : tactic expr :=
do let decl := func.decl,
   let intl := internal_expr func,
   let arity := func.live_params.length,
   α ← mk_local_def `α $ @expr.const tt ``typevec [func.vec_lvl] `(arity),
   β ← mk_local_def `β $ @expr.const tt ``typevec [func.vec_lvl] `(arity),
   f ← mk_app ``typevec.arrow [α,β] >>= mk_local_def `f,
   let r := expr.imp (intl α) (intl β),

   map_t ← pis (func.dead_params.map prod.fst ++ [α,β,f]) r,
   (_,df) ← @solve_aux unit map_t $ do
     { vs ← intron' func.dead_params.length,
       let vs := vs.zip $ func.dead_params.map prod.snd,
       mαβf ← destruct_typevec func `α,
       let m := rb_map.of_list $ mαβf.map $ λ ⟨α,β,f,i⟩, (α,f),
       let β := mαβf.map $ λ ⟨α,β,f,i⟩, (β,i),
       target >>= instantiate_mvars >>= unsafe_change,
       let e := (@expr.const tt func.eqn_name func.decl.univ_levels),
       g ← target,
       (g',_) ← solve_aux g $
         repeat (rewrite_target e) >> target,
       unsafe_change g',
       x ← intro1,
       xs ← cases_core x,
       xs.mmap' $ λ ⟨c, args, _⟩, do
         { let e := (@expr.const tt c decl.univ_levels).mk_app $ mk_arg_list (vs ++ β),
           args' ← args.mmap (map_arg m),
           exact $ e.mk_app args' } },
   df ← instantiate_mvars df,
   add_decl' $ declaration.defn func.map_name decl.univ_params map_t df (reducibility_hints.regular 1 tt) decl.is_trusted

meta def mk_mvfunctor_map_eqn (func : internal_mvfunctor) : tactic unit :=
do env ← get_env,
   let decl := func.decl,
   let cs := env.constructors_of func.decl.to_name,
   live_params' ← func.live_params.mmap $ λ ⟨v,i⟩, flip prod.mk i <$> (infer_type v >>= mk_local_def (add_prime v.local_pp_name)),
   let arity := live_params'.length,
   fs ← mzip_with (λ v v' : expr × ℕ, prod.mk v.1 <$> mk_local_def ("f" ++ to_string v.2 : string) (v.1.imp v'.1)) func.live_params live_params',
   let m := rb_map.of_list fs,
   cs.enum.mmap' $ λ ⟨i,c⟩, do
     { let c := @expr.const tt c func.decl.univ_levels,
       let e := c.mk_app func.params,
       let e' := c.mk_app $ mk_arg_list $ func.dead_params ++ live_params',
       t  ← infer_type e,
       (vs,_) ← mk_local_pis t,
       t' ← infer_type e',
       vs' ← vs.mmap (map_arg m),
       α ← mk_live_vec func.vec_lvl (mk_arg_list func.live_params),
       β ← mk_live_vec func.vec_lvl (mk_arg_list live_params'),
       f ← mk_map_vec func.vec_lvl $ fs.map prod.snd,
       let x := e.mk_app vs,
       let map_e := (@expr.const tt func.map_name func.decl.univ_levels).mk_app (mk_arg_list func.dead_params ++ [α,β,f,x]),
       eqn ← mk_app `eq [map_e,(e'.mk_app vs')] >>= pis (func.params ++ live_params'.map prod.fst ++ fs.map prod.snd ++ vs),
       (_,pr) ← solve_aux eqn $ do
         { intros >> reflexivity },
       pr ← instantiate_mvars pr,
       add_decl $ declaration.thm (func.map_name <.> ("_equation_" ++ to_string i)) decl.univ_params eqn (pure pr),
       pure () }

meta def mk_mvfunctor_instance (func : internal_mvfunctor) : tactic unit :=
do map_d ← mk_mvfunctor_map func,
   mk_mvfunctor_map_eqn func,
   vec ← mk_live_vec func.vec_lvl $ func.live_params.map prod.fst,
   let decl := func.decl,
   let intl := (@expr.const tt func.def_name decl.univ_levels).mk_app (func.dead_params.map prod.fst),
   let vs := (func.dead_params.map prod.fst),

   t ← mk_app ``mvfunctor [intl] >>= pis vs,
   (_,df) ← @solve_aux unit t $ do
     { vs ← intro_lst $ vs.map expr.local_pp_name,
       to_expr ``( { mvfunctor . map := %%(map_d.mk_app vs) } ) >>= exact },
   df ← instantiate_mvars df,
   let inst_n := func.def_name <.> "mvfunctor",
   add_decl $ declaration.defn inst_n func.decl.univ_params t df (reducibility_hints.regular 1 tt) func.decl.is_trusted,
   mk_const inst_n >>= infer_type >>= trace,
   set_basic_attribute `instance inst_n,
   pure ()

open expr (const)

meta def mk_head_t (decl : inductive_type) (func : internal_mvfunctor) : lean.parser inductive_type :=
do let n := decl.name,
   let head_n := (n <.> "head_t"),
   let sig_c  : expr := const n decl.u_params,
   cs ← decl.ctors.mmap $ λ d : type_cnstr,
   do { vs' ← d.args.mfilter $ λ v,
          do { t ← infer_type v,
               pure $ ¬ ∃ v ∈ func.live_params, expr.occurs (prod.fst v) t },
        pure { name := d.name.update_prefix head_n, args := vs', .. d } },
   let decl' := { name := head_n, ctors := cs, params := func.dead_params.map prod.fst, .. decl },
   decl' <$ mk_inductive' decl'

meta def mk_child_t (decl : inductive_type) (func : internal_mvfunctor) : lean.parser (list inductive_type) :=
do let n := decl.name,
   let mk_constr : name → expr := λ n', (const (n'.update_prefix $ n <.> "head_t") decl.u_params).mk_app $ func.dead_params.map prod.fst,
   let head_t : expr := const (n <.> "head_t") decl.u_params,
   func.live_params.mmap $ λ l,
     do let child_n := (n <.> "child_t" ++ l.1.local_pp_name),
        let sig_c  : expr := const n decl.u_params,
        cs ← (decl.ctors.mmap $ λ d : type_cnstr,
          do { (rec,vs') ← d.args.mpartition $ λ v,
                 do { t ← infer_type v,
                      pure $ expr.occurs l.1 t },
               vs' ← vs'.mfilter $ λ v,
                 do { t ← infer_type v,
                      pure $ ¬ ∃ v ∈ func.live_params, expr.occurs (prod.fst v) t },
               rec.enum.mmap $ λ ⟨i,r⟩, do
                 (args',r') ← infer_type r >>= unpi,
                 pure { name := (d.name.append_after i).update_prefix $ n <.> "child_t"  ++ l.1.local_pp_name,
                        args := vs' ++ args', result := [(mk_constr d.name).mk_app vs'], .. d } } : tactic _),
        idx ← (mk_local_def `i $ head_t.mk_app $ func.dead_params.map prod.fst : tactic _),
        let decl' := { name := child_n, params := func.dead_params.map prod.fst, idx := decl.idx ++ [idx], ctors := cs.join, .. decl },
        decl' <$ mk_inductive' decl'

meta def inductive_type.of_pfunctor (func : internal_mvfunctor) : lean.parser inductive_type :=
do -- mk_inductive' func.induct,
   let d := func.decl,
   let params := func.params,
   (idx,t) ← unpi (d.type.instantiate_pi params),
   env ← get_env,
   -- let (params,idx) := idx.split_at $ env.inductive_num_params d.to_name,
   cs ← (env.constructors_of d.to_name).mmap $ λ c : name,
   do { let e := @const tt c d.univ_levels,
        t ← infer_type $ e.mk_app params,
        (vs,t) ← unpi t,
        pure (t.get_app_fn.const_name,{ type_cnstr .
               name := c,
               args := vs,
               result := t.get_app_args.drop $ env.inductive_num_params d.to_name }) },
   pure { pre     := func.induct.pre,
          name    := d.to_name,
          u_names := d.univ_params,
          params  := params,
          idx     := idx, type := t,
          ctors   := cs.map prod.snd }

meta def mk_child_t_vec (decl : inductive_type) (func : internal_mvfunctor) (vs : list inductive_type) : lean.parser expr :=
do let n := decl.name,
   let head_t := (@const tt (n <.> "head_t") func.decl.univ_levels).mk_app $ func.dead_params.map prod.fst,
   let child_n := (n <.> "child_t"),
   let arity := func.live_params.length,
   punit.star ← coe $
     do { hd_v ← mk_local_def `hd head_t,
          (expr.sort u') ← pure decl.type,
          let u := u'.pred,
          let vec_t := @const tt ``typevec [u] (reflect arity),
          t ← pis (func.dead_params.map prod.fst ++ [hd_v]) vec_t,
          nil ← mk_mapp ``fin.elim0 [some $ expr.sort u.succ],
          trace "bar",
          vec ← func.live_params.mfoldr (λ e v,
            do c ← mk_const $ child_n ++ e.1.local_pp_name,
               let c := (@const tt (n <.> "child_t" ++ e.1.local_pp_name) func.decl.univ_levels).mk_app $ func.dead_params.map prod.fst ++ [hd_v],
               mv ← mk_mvar,
               unify_app (const ``append1 [u]) [mv,v,c]) nil,
          -- vec ← mk_mapp ``_root_.id [vec_t,vec],
          df ← (instantiate_mvars vec >>= lambdas (func.dead_params.map prod.fst ++ [hd_v]) : tactic _),
          -- df ← instantiate_mvars vec,
          -- trace df,
          let r := reducibility_hints.regular 1 tt,
          add_decl' $ declaration.defn child_n func.decl.univ_params t df r tt,
          -- pure { eqn_compiler.fun_def .
          --        univs := func.induct.u_names,
          --        name := child_n,
          --        params := func.dead_params.map prod.fst ++ [hd_v],
          --        type := vec_t,
          --        body := eqn_compiler.def_body.term df }
          pure () },
   trace func.decl.to_name,
   -- eqn_compiler.add_fn func.decl.to_name eqns,
   pure $ expr.const child_n $ func.induct.u_params

meta def mk_pfunctor (func : internal_mvfunctor) : lean.parser unit :=
do d ← inductive_type.of_pfunctor func,
   hd ← mk_head_t d func,
   ch ← mk_child_t d func,
   mk_child_t_vec d func ch,
   let arity := func.live_params.length,
   (expr.sort u') ← pure d.type,
   let u := u'.pred,
   let vec_t := @const tt ``mvpfunctor [u] $ reflect arity,
   t ← pis (func.dead_params.map prod.fst) vec_t,
   let n := d.name,
   let head_t := (@const tt (n <.> "head_t") func.decl.univ_levels).mk_app $ func.dead_params.map prod.fst,
   let child_t := (@const tt (n <.> "child_t") func.decl.univ_levels).mk_app $ func.dead_params.map prod.fst,
   trace "foo",
   (infer_type child_t >>= trace : tactic _),
   df ← (mk_mapp ``mvpfunctor.mk [some $ reflect arity, head_t,child_t] >>= lambdas (func.dead_params.map prod.fst) : tactic _),
   add_decl $ mk_definition func.pfunctor_name func.decl.univ_params t df,
   pure ()

meta def mk_pfunc_constr (func : internal_mvfunctor) : tactic unit :=
do env ← get_env,
   let cs := env.constructors_of func.decl.to_name,
   let u := func.type.sort_univ.pred,
   let u' := func.univ_params.foldl level.max u,
   let out_t :=  (@const tt func.pfunctor_name func.univ_params).mk_app $ func.dead_params.map prod.fst,
   vec_t ← mk_live_vec func.vec_lvl $ func.live_params.map prod.fst,
   let arity := func.live_params.length,
   let fn := @const tt ``mvpfunctor.apply [u],
   r ← unify_app fn [reflect arity,out_t,vec_t],
   cs.mmap $ λ c,
     do { let p := c.update_prefix (c.get_prefix <.> "pfunctor"),
          let hd_c := c.update_prefix (func.decl.to_name <.> "head_t"),
          let e := (@const tt c func.univ_params).mk_app func.params,
          (args,_) ← infer_type e >>= mk_local_pis,
          sig ← pis (func.params ++ args) r,
          (rec,vs') ← args.mpartition $ λ v,
                 do { t ← infer_type v,
                      pure $ ¬ ∃ v ∈ func.live_params, expr.occurs (prod.fst v) t },

          let e := (@const tt hd_c func.univ_params).mk_app (func.dead_params.map prod.fst ++ rec),
          ms ← func.live_params.mmap $ λ l,
                do { let l_name := l.1.local_pp_name,
                     vs' ← vs'.mfilter $ λ v,
                       do { t ← infer_type v,
                            pure $ expr.occurs l.1 t },
                     let ch_t := (@const tt (func.decl.to_name <.> "child_t" ++ l_name) func.univ_params).mk_app (func.dead_params.map prod.fst ++ [e]),
                     let ch_c := c.update_prefix (func.decl.to_name <.> "child_t" ++ l_name),
                     let t := ch_t.imp l.1,
                     (_,f) ← @solve_aux unit t $ do
                       { interactive.generalize `hy () (to_pexpr e,`y),
                         x ← intro `x,
                         focus1 $ do
                         { a ← better_induction x,
                           a.mmap' $ λ ⟨ctor,a,b⟩,
                           do { hy ← get_local `hy,
                                let no_conf := func.decl.to_name <.> "head_t" <.> "no_confusion",
                                tgt ← target,
                                mk_mapp no_conf (func.dead_params.map (some ∘ prod.fst) ++ [tgt,none,none,hy]) >>= apply,
                                vs'.mmap $ λ v, do {
                                  try $ intro1 >>= subst,
                                  exact (v.mk_app $ a.map prod.fst) <|> exact v } } } },
                     pure f },
          (_,df) ← solve_aux r $ do
            { m ← mk_map_vec func.vec_lvl ms,
              refine ``( ⟨ %%e, _ ⟩ ),
              exact m,
              pure () },
          let c' := c.update_prefix $ c.get_prefix <.> "mvpfunctor",
          -- trace c',
          let vs := func.params ++ args,
          -- trace $ vs.map expr.local_uniq_name,
          -- trace $ r.list_local_consts.map expr.local_uniq_name,
          -- trace $ df.list_local_consts.map expr.local_uniq_name,
          -- trace $ args.map expr.local_uniq_name,
          r  ← pis vs r >>= instantiate_mvars,
          df ← instantiate_mvars df >>= lambdas vs,
          -- trace df.list_local_consts,
          -- let df := r.mk_sorry,
          -- args.mmap infer_type >>= trace,
          -- trace r,
          add_decl $ mk_definition c' func.decl.univ_params r df,
          pure () },
   pure ()

meta def saturate' : expr → expr → tactic expr
| (expr.pi n bi t b) e :=
do v ← mk_meta_var t,
   t ← whnf $ b.instantiate_var v,
   saturate' t (e v)
| t e := pure e

meta def saturate (e : expr) : tactic expr :=
do t ← infer_type e >>= whnf,
   saturate' t e
-- #check typevec_cases_cons₃

meta def destruct_multimap : expr → tactic unit
| e :=
do `(%%t ⟹ _) ← infer_type e,
   `(typevec %%n) ← infer_type t, trace n,
    if ¬ n.is_napp_of ``has_zero.zero 1
      then do
        refine ``(typevec_cases_cons₂ %%n _ _ _ _ _ %%e),
        f ← intro `f, e' ← intro1,
        trace "*", trace_state,
        destruct_multimap e'
      else pure ()

meta def mk_pfunc_recursor (func : internal_mvfunctor) : tactic unit :=
do let u := fresh_univ func.induct.u_names,
   v ← mk_live_vec func.vec_lvl $ func.live_params.map prod.fst,
   fn ← mk_app `mvpfunctor.apply [functor_expr func,v],
   C ← mk_local' `C binder_info.implicit (expr.imp fn $ expr.sort $ level.param u),
   cases_t ← func.induct.ctors.mmap $ λ c,
   do { let n := c.name.update_prefix (func.decl.to_name <.> "mvpfunctor"),
        let e := (@expr.const tt n func.induct.u_params).mk_app (func.params ++ c.args),
        pis c.args (C e) >>= mk_local_def `v },
   n ← mk_local_def `n fn,
   trace "-",
   (_,df) ← solve_aux (expr.pis [n] $ C n) $ do
     { n ← intro1, [(_, [x,y], _)] ← cases_core n,
       infer_type x >>= trace,
       infer_type y >>= trace,
       cases x, gs ← get_goals, -- case distinction of n_snd as a vector
       gs ← mzip_with (λ h g,
         do { set_goals [g],
              admit,
              -- h ← note `h none h >>= saturate,
              -- n_snd ← get_local `n_snd,
              -- trace "+",
              -- `[dsimp [list_F''.pfunctor]],
              -- destruct_multimap n_snd,
              -- refine ``(typevec_cases_cons₂ 0 _ _ _ _ _ %%n_snd),
              -- to_expr ``(foo %%C _ (%%h )) >>= apply,

              get_goals }) cases_t gs,
       set_goals gs.join,
       trace_state },
   let vs := func.params.map expr.to_implicit_binder ++ C :: cases_t,
   df ← instantiate_mvars df >>= lambdas vs,
   t ← pis (vs ++ [n]) (C n),
   trace "-",
   trace t,
   add_decl $ declaration.thm (func.pfunctor_name <.> "rec") (u :: func.induct.u_names) t (pure df),
   trace "-",
   pure ()

#print internal_mvfunctor

meta def mk_qpf_abs (func : internal_mvfunctor) : tactic unit :=
do let n := func.live_params.length,
   let dead_params := func.dead_params.map prod.fst,
   let e := (@const tt func.def_name func.induct.u_params).mk_app dead_params,
   let e' := (@const tt func.pfunctor_name func.induct.u_params).mk_app dead_params,
   t ← to_expr ``(∀ v, mvpfunctor.apply %%e' v → %%e v) >>= pis dead_params,
   let df := t.mk_sorry,
   add_decl $ mk_definition func.abs_name func.induct.u_names t df

meta def mk_qpf_repr (func : internal_mvfunctor) : tactic unit :=
do let n := func.live_params.length,
   let dead_params := func.dead_params.map prod.fst,
   let e := (@const tt func.def_name func.induct.u_params).mk_app dead_params,
   let e' := (@const tt func.pfunctor_name func.induct.u_params).mk_app dead_params,
   t ← to_expr ``(∀ v, %%e v → mvpfunctor.apply %%e' v) >>= pis dead_params,
   let df := t.mk_sorry,
   add_decl $ mk_definition func.repr_name func.induct.u_names t df

-- meta def mk_pfunc_mvfunctor_instance (func : internal_mvfunctor) : tactic unit :=
-- do let n := func.live_params.length,
--    let dead_params := func.dead_params.map prod.fst,
--    let e := (@const tt func.def_name func.induct.u_params).mk_app dead_params,
--    mvfunctor_t ← mk_mapp ``mvfunctor [some (reflect n),e],
--    (_,df) ← solve_aux mvfunctor_t $ do
--      { admit },
--    df ← instantiate_mvars df >>= lambdas dead_params,
--    mvfunctor_t ← instantiate_mvars mvfunctor_t,
--    let inst_n := func.def_name <.> "mvfunctor",
--    add_decl $ mk_definition inst_n func.induct.u_names mvfunctor_t df,
--    set_basic_attribute `instance inst_n

meta def mk_mvqpf_instance (func : internal_mvfunctor) : tactic unit :=
do let n := func.live_params.length,
   let dead_params := func.dead_params.map prod.fst,
   let e := (@const tt func.def_name func.induct.u_params).mk_app dead_params,
   let abs_fn := (@const tt func.abs_name func.induct.u_params).mk_app dead_params,
   let repr_fn := (@const tt func.repr_name func.induct.u_params).mk_app dead_params,
   mk_qpf_abs func,
   mk_qpf_repr func,
   pfunctor_i ← mk_mapp ``mvfunctor [some (reflect n),e] >>= mk_instance,
   mvqpf_t ← mk_mapp ``mvqpf [some (reflect n),e,pfunctor_i] >>= instantiate_mvars,
   infer_type mvqpf_t >>= trace,
   (_,df) ← solve_aux mvqpf_t $ do
     { let p := (@const tt func.pfunctor_name func.induct.u_params).mk_app dead_params,
       refine ``( { P := %%p, abs := %%abs_fn, repr' := %%repr_fn, .. } ),
       admit, admit },
   df ← instantiate_mvars df >>= lambdas dead_params,
   mvqpf_t ← pis dead_params mvqpf_t,
   let inst_n := func.def_name <.> "mvqpf",
   add_decl $ mk_definition inst_n func.induct.u_names mvqpf_t df,
   set_basic_attribute `instance inst_n
-- #exit
-- @[derive_handler] meta def qpf_derive_handler : derive_handler :=
-- λ p n,
-- if p.is_constant_of ``mvqpf then
-- do func ← mk_internal_functor n,
--    mk_mvfunctor_instance func,
--    mk_pfunctor func,
--    mk_pfunc_constr func,
--    pure tt
-- else pure ff

open interactive lean.parser lean

@[user_command]
meta def qpf_decl (meta_info : decl_meta_info) (_ : parse (tk "qpf")) : parser unit :=
do d ← inductive_decl.parse meta_info,
   func ← mk_internal_functor' d,
   mk_mvfunctor_instance func,
   mk_pfunctor func,
   mk_pfunc_constr func,
   mk_pfunc_recursor func,
   -- mk_pfunc_map func,
   -- mk_pfunc_mvfunctor_instance func,
   mk_mvqpf_instance func,
   pure ()

-- local attribute [user_command]  qpf_decl

end tactic

namespace hidden

universes u_1 u_2 u_3

-- set_option trace.app_builder true
-- set_option pp.universes true

-- @[derive mvqpf]
qpf list_F (α : Type)
| nil : list_F
| cons : ℤ → α → list_F

-- #exit
-- -- #print hidden.list_F.head_t
-- #print prefix hidden.list_F
-- #print hidden.list_F.child_t
-- -- #print hidden.list_F.pfunctor

-- -- #test list_F.internal_eq
-- -- #test @list_F.map

-- example : ∀ (α : Type), list_F.internal (typevec.of_ind (typevec.ind.cons α typevec.ind.nil)) = list_F α :=
-- list_F.internal_eq

-- example : Π (α β : typevec 1), α ⟹ β → list_F.internal α → list_F.internal β :=
-- list_F.internal.map

-- -- #test hidden.list_F.internal.map._equation_0
-- -- #test hidden.list_F.internal.map._equation_1

-- example : ∀ (α α' : Type) (f0 : α → α'),
--   list_F.internal.map (typevec.of_ind (typevec.ind.cons α typevec.ind.nil))
--       (typevec.of_ind (typevec.ind.cons α' typevec.ind.nil))
--       (typevec.append_fun typevec.nil_fun f0)
--       _ =
--     list_F.nil α' :=
-- list_F.internal.map._equation_0

-- example : ∀ (α α' : Type) (f0 : α → α') (a : ℤ) (a_1 : α),
--   list_F.internal.map (typevec.of_ind (typevec.ind.cons α typevec.ind.nil))
--       (typevec.of_ind (typevec.ind.cons α' typevec.ind.nil))
--       (typevec.append_fun typevec.nil_fun f0)
--       _ =
--     list_F.cons a (f0 a_1) :=
-- list_F.internal.map._equation_1


-- @[derive mvqpf]

-- @[user_command]
-- meta def my_cmd (_ : interactive.parse (lean.parser.tk "my_cmd")) : lean.parser unit :=
-- do lean.parser.with_input lean.parser.command_like
-- "inductive list_F (a : Type)
-- | nil : list_F",
--    pure ().

-- my_cmd

-- #check @list_F.no_confusion

-- -- #print hidden.list_F'.head_t
-- -- #print hidden.list_F'.child_t.α
-- -- #print hidden.list_F'.child_t.β
-- -- #print hidden.list_F'.child_t
-- -- #print hidden.list_F'.pfunctor

-- -- #test list_F'.internal_eq
-- -- #test @list_F'.map

-- example : ∀ (α β : Type),
--   list_F'.internal (typevec.of_ind (typevec.ind.cons α (typevec.ind.cons β typevec.ind.nil))) = list_F' α β :=
-- list_F'.internal_eq

-- example : Π (α β : typevec 2), α ⟹ β → list_F'.internal α → list_F'.internal β :=
-- list_F'.internal.map

-- -- #test hidden.list_F'.internal.map._equation_0
-- -- #test hidden.list_F'.internal.map._equation_1

-- example : ∀ (α β α' β' : Type) (f0 : α → α') (f1 : β → β'),
--   list_F'.internal.map (typevec.of_ind (typevec.ind.cons α (typevec.ind.cons β typevec.ind.nil)))
--       (typevec.of_ind (typevec.ind.cons α' (typevec.ind.cons β' typevec.ind.nil)))
--       (typevec.append_fun (typevec.append_fun typevec.nil_fun f1) f0)
--       _ =
--     list_F'.nil α' β' :=
-- list_F'.internal.map._equation_0

-- example : ∀ (α β α' β' : Type) (f0 : α → α') (f1 : β → β') (a : α) (a_1 : β),
--   list_F'.internal.map (typevec.of_ind (typevec.ind.cons α (typevec.ind.cons β typevec.ind.nil)))
--       (typevec.of_ind (typevec.ind.cons α' (typevec.ind.cons β' typevec.ind.nil)))
--       (typevec.append_fun (typevec.append_fun typevec.nil_fun f1) f0)
--       _ =
--     list_F'.cons (f0 a) (f1 a_1) :=
-- list_F'.internal.map._equation_1

-- @[derive mvqpf]
qpf list_F'' (α β γ : Type u)
| nil : (β → γ) → list_F''
| cons : (α → β) → list_F''

-- #exit
-- #print hidden.list_F''.head_t
-- #print hidden.list_F''.child_t.γ
-- #print hidden.list_F''.child_t
-- #print hidden.list_F''.pfunctor

-- #check list_F''.internal_eq
-- #check @list_F''.map

example : ∀ (α : Type*) (β : Type*) (γ : Type*),
    list_F''.internal α β (typevec.of_ind (typevec.ind.cons γ typevec.ind.nil)) = list_F'' α β γ :=
list_F''.internal_eq

example : Π (α : Type*) (β : Type*) (α_1 β_1 : typevec 1),
    α_1 ⟹ β_1 → list_F''.internal α β α_1 → list_F''.internal α β β_1 :=
@list_F''.internal.map

-- #test hidden.list_F''.internal.map._equation_0
-- #test hidden.list_F''.internal.map._equation_1

-- #check list_F''.internal.map

example : ∀ (α : Type u_1) (β : Type u_1) (γ γ' : Type u_1) (f2 : γ → γ') (a : β → γ),
  list_F''.internal.map α β (typevec.of_ind (typevec.ind.cons γ typevec.ind.nil))
      (typevec.of_ind (typevec.ind.cons γ' typevec.ind.nil))
      (typevec.append_fun typevec.nil_fun f2)
      _ =
    list_F''.nil α (λ (a_1 : β), f2 (a a_1)) :=
list_F''.internal.map._equation_0

example : ∀ (α : Type u_1) (β : Type u_1) (γ γ' : Type u_1) (f2 : γ → γ') (a : α → β),
  list_F''.internal.map α β (typevec.of_ind (typevec.ind.cons γ typevec.ind.nil))
      (typevec.of_ind (typevec.ind.cons γ' typevec.ind.nil))
      (typevec.append_fun typevec.nil_fun f2)
      _ =
    list_F''.cons γ' (λ (a_1 : α), a a_1) :=
list_F''.internal.map._equation_1

-- @[derive mvqpf]
qpf list_F''' (α β γ : Type u)
| nil : list_F'''
| cons : (γ → β) → list_F'''

-- #exit
-- #print hidden.list_F'''.head_t
-- #print hidden.list_F'''.child_t.α
-- #print hidden.list_F'''.child_t.β
-- #print hidden.list_F'''.child_t
-- #print hidden.list_F'''.pfunctor

-- #check list_F'''.internal_eq
-- #check @list_F'''.map

-- example : ∀ (α β γ : Type*),
--     list_F'''.internal γ (typevec.of_ind (typevec.ind.cons α (typevec.ind.cons β typevec.ind.nil))) =
--       list_F''' α β γ :=
-- list_F'''.internal_eq

-- example : Π (γ : Type*) (α β : typevec 2), α ⟹ β → list_F'''.internal γ α → list_F'''.internal γ β :=
-- @list_F'''.internal.map

-- -- #test hidden.list_F'''.internal.map._equation_0
-- -- #test hidden.list_F'''.internal.map._equation_1

-- example : ∀ (α β γ α' β' : Type u) (f0 : α → α') (f1 : β → β'),
--   list_F'''.internal.map γ (typevec.of_ind (typevec.ind.cons α (typevec.ind.cons β typevec.ind.nil)))
--       (typevec.of_ind (typevec.ind.cons α' (typevec.ind.cons β' typevec.ind.nil)))
--       (typevec.append_fun (typevec.append_fun typevec.nil_fun f1) f0)
--       _ = --(list_F'''.nil α β γ) =
--     list_F'''.nil α' β' γ :=
-- list_F'''.internal.map._equation_0

-- example : ∀ (α β γ α' β' : Type u) (f0 : α → α') (f1 : β → β') (a : γ → β),
--   list_F'''.internal.map γ (typevec.of_ind (typevec.ind.cons α (typevec.ind.cons β typevec.ind.nil)))
--       (typevec.of_ind (typevec.ind.cons α' (typevec.ind.cons β' typevec.ind.nil)))
--       (typevec.append_fun (typevec.append_fun typevec.nil_fun f1) f0)
--       ( _ ) =
--     list_F'''.cons α' (λ (a_1 : γ), f1 (a a_1)) :=
-- list_F'''.internal.map._equation_1

-- @[derive mvqpf]
qpf list_F'''' (α β γ : Type u)
| nil : (β → γ) → (γ → α) → list_F''''
| cons : (α → β) → list_F''''

#check hidden.list_F'''.mvpfunctor.cons

-- #print hidden.list_F''''.head_t
-- #print hidden.list_F''''.child_t
-- #print hidden.list_F''''.pfunctor

-- #check @list_F''''.internal_eq
-- #check @list_F''''.internal.map

example : ∀ (α : Type*) (β : Type*) (γ : Type*),
    list_F''''.internal α β γ (typevec.of_ind typevec.ind.nil) = list_F'''' α β γ :=
@list_F''''.internal_eq

example : Π (α : Type*) (β : Type*) (γ : Type*) (α_1 β_1 : typevec 0),
    α_1 ⟹ β_1 → list_F''''.internal α β γ α_1 → list_F''''.internal α β γ β_1 :=
@list_F''''.internal.map

-- #test hidden.list_F''''.internal.map._equation_0

example : ∀ (α : Type u_1) (β : Type u_1) (γ : Type u_1) (a : β → γ) (a_1 : γ → α),
  list_F''''.internal.map α β γ ⦃ ⦄ ⦃ ⦄ typevec.nil_fun
      _ =
    list_F''''.nil (λ (a_1 : β), a a_1) (λ (a : γ), a_1 a) :=
list_F''''.internal.map._equation_0

example : ∀ (α : Type u_1) (β : Type u_1) (γ : Type u_1) (a : α → β),
  list_F''''.internal.map α β γ (⦃ ⦄) ( ⦃ ⦄ ) typevec.nil_fun
      _ =
    list_F''''.cons γ (λ (a_1 : α), a a_1) :=
list_F''''.internal.map._equation_1

-- data list
-- | nil : list
-- | cons : ℤ → list → list

end hidden