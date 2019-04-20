
import data.fix.inductive_decl
import mvqpf
import data.fix.equations
import category.bitraversable.instances

universes u


namespace tactic

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

meta def find_dead_occ (n : name) (ps : list expr) : rb_map expr ℕ → expr → rb_map expr ℕ
| m `(%%a → %%b) := find_dead_occ (a.list_local_consts.foldl rb_map.erase m) b
| m (expr.local_const _ _ _ _) := m
| m e :=
if e.get_app_fn.const_name = n
  then m
  else e.list_local_consts.foldl rb_map.erase m

meta def live_vars (induct : inductive_type) : tactic $ rb_map expr ℕ × rb_map expr ℕ :=
do let n := induct.name,
   let params : list expr := induct.params,
   let e := (@expr.const tt n induct.u_params).mk_app params,
   let vs := rb_map.of_list $ params.enum.map prod.swap,
   let ls := induct.ctors,
   ls ← ls.mmap $ λ c,
     do { ts ← c.args.mmap infer_type,
          pure $ ts.foldl (find_dead_occ n params) vs },
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

meta def inductive_type.to_format (decl : inductive_type) : tactic format :=
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
   return xs

meta def mk_inductive' : inductive_type → lean.parser unit
| decl :=
do xs ← decl.to_format,
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
   (m,m') ← live_vars ind,
   let m := rb_map.sort prod.snd m.to_list,
   let m' := rb_map.sort prod.snd m'.to_list,
   u ← mk_meta_univ,
   let vars := string.intercalate "," (m.map to_string),
   (params.mmap' (λ e, infer_type e >>= unify (expr.sort u))
     <|> fail format!"live type parameters ({params}) are not in the same universe" : tactic _),
   (level.succ u) ← get_univ_assignment u <|> pure level.zero.succ,
   ts ← (params.mmap infer_type : tactic _),
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

notation `⦃ ` r:( foldr `, ` (h t, typevec.append1 t h) fin'.elim0 ) ` ⦄` := r
notation `⦃`  `⦄` := fin'.elim0

local prefix `♯`:0 := cast (by try { simp only with typevec }; congr' 1; try { simp only with typevec })

meta def mk_internal_functor_def (func : internal_mvfunctor) : tactic unit :=
do let trusted := func.decl.is_trusted,
   let arity := func.live_params.length,
   let vec := @expr.const tt ``_root_.typevec [func.vec_lvl] `(arity),
   v_arg ← mk_local_def `v_arg vec,
   t ← pis (func.dead_params.map prod.fst ++ [v_arg]) func.type,
   (_,df) ← @solve_aux unit t $ do
     { m' ← func.dead_params.mmap $ λ v, prod.mk v.2 <$> intro v.1.local_pp_name,
       vs ← func.live_params.reverse.mmap $ λ x, do
         { refine ``(typevec.typevec_cases_cons _ _),
           x' ← intro x.1.local_pp_name,
           pure (x.2,x') },
       refine ``(typevec.typevec_cases_nil _),
       let args := (rb_map.sort prod.fst (m' ++ vs)).map prod.snd,
       let e := (@expr.const tt func.decl.to_name (func.decl.univ_params.map level.param)).mk_app args,
       exact e },
   df ← instantiate_mvars df,
   add_decl $ declaration.defn func.def_name func.decl.univ_params t df (reducibility_hints.regular 1 tt) trusted

meta def mk_live_vec (u : level) (vs : list expr) : tactic expr :=
do nil ← mk_mapp ``fin'.elim0 [@expr.sort tt $ level.succ u],
   vs.reverse.mfoldr (λ e s, mk_mapp ``typevec.append1 [none,s,e]) nil

meta def mk_map_vec (u u' : level) (vs : list expr) : tactic expr :=
do nil  ← mk_mapp ``fin'.elim0 [some $ expr.sort u.succ],
   nil' ← mk_mapp ``fin'.elim0 [some $ expr.sort u'.succ], --  [u.succ.succ] (expr.sort u.succ),
   nil_fun ← mk_mapp ``typevec.nil_fun [nil,nil'],
   vs.reverse.mfoldr (λ e s, do
     app ← mk_const ``typevec.append_fun,
     mk_mapp ``typevec.append_fun [none,none,none,none,none,s,e]) nil_fun


meta def mk_internal_functor_app (func : internal_mvfunctor) : tactic expr :=
do let decl := func.decl,
   vec ← mk_live_vec func.vec_lvl $ func.live_params.map prod.fst,
   pure $ (@expr.const tt func.def_name decl.univ_levels).mk_app (func.dead_params.map prod.fst ++ [vec])

meta def mk_internal_functor_eqn (func : internal_mvfunctor) : tactic unit :=
do let decl := func.decl,
   lhs ← mk_internal_functor_app func,
   let rhs := (@expr.const tt decl.to_name decl.univ_levels).mk_app func.params,
   p ← mk_app `eq [lhs,rhs] >>= pis func.params,
   pr ← solve_async [] p $ intros >> reflexivity,
   add_decl $ declaration.thm func.eqn_name decl.univ_params p pr

-- meta def mk_internal_functor (n : name) : tactic internal_mvfunctor :=
-- do decl ← get_decl n,
--    func ← internalize_mvfunctor decl,
--    mk_internal_functor_def func,
--    mk_internal_functor_eqn func,
--    pure func

meta def mk_internal_functor' (d : interactive.inductive_decl) : lean.parser internal_mvfunctor :=
do d ← inductive_type.of_decl d,
   mk_inductive' d,
   func ← internalize_mvfunctor d,
   mk_internal_functor_def func,
   mk_internal_functor_eqn func,
   pure func

open typevec

meta def destruct_typevec₃ (func : internal_mvfunctor) (v : name) : tactic (list $ expr × expr × expr × ℕ) :=
do vs ← func.live_params.reverse.mmap $ λ x : expr × ℕ, do
     { refine ``(typevec_cases_cons₃ _ _),
       α ← get_unused_name `α >>= intro,
       β ← get_unused_name `β >>= intro,
       f ← get_unused_name `f >>= intro,
       pure (α,β,f,x.2) },
   refine ``(typevec_cases_nil₃ _),
   pure vs

meta def destruct_typevec' (func : internal_mvfunctor) (v : name) : tactic (list $ expr × ℕ) :=
do vs ← func.live_params.reverse.mmap $ λ x : expr × ℕ, do
     { refine ``(typevec_cases_cons _ _),
       α ← get_unused_name `α >>= intro,
       pure (α,x.2) },
   refine ``(typevec_cases_nil _),
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
       mαβf ← destruct_typevec₃ func `α,
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
       f ← mk_map_vec func.vec_lvl func.vec_lvl $ fs.map prod.snd,
       let x := e.mk_app vs,
       let map_e := (@expr.const tt func.map_name func.decl.univ_levels).mk_app (mk_arg_list func.dead_params ++ [α,β,f,x]),
       eqn ← mk_app `eq [map_e,(e'.mk_app vs')] >>= pis (func.params ++ live_params'.map prod.fst ++ fs.map prod.snd ++ vs) >>= instantiate_mvars,
       pr ← solve_async [] eqn $ do
         { intros >> reflexivity },
       let n := func.map_name <.> ("_equation_" ++ to_string i),
       add_decl $ declaration.thm n decl.univ_params eqn pr,
       simp_attr.typevec.set n () tt,
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
          nil ← mk_mapp ``fin'.elim0 [some $ expr.sort u.succ],
          vec ← func.live_params.reverse.mfoldr (λ e v,
            do c ← mk_const $ child_n ++ e.1.local_pp_name,
               let c := (@const tt (n <.> "child_t" ++ e.1.local_pp_name) func.decl.univ_levels).mk_app $ func.dead_params.map prod.fst ++ [hd_v],
               mv ← mk_mvar,
               unify_app (const ``append1 [u]) [mv,v,c]) nil,
          -- vec ← mk_mapp ``_root_.id [vec_t,vec],
          df ← (instantiate_mvars vec >>= lambdas (func.dead_params.map prod.fst ++ [hd_v]) : tactic _),
          -- df ← instantiate_mvars vec,
          let r := reducibility_hints.regular 1 tt,
          add_decl' $ declaration.defn child_n func.decl.univ_params t df r tt,
          -- pure { eqn_compiler.fun_def .
          --        univs := func.induct.u_names,
          --        name := child_n,
          --        params := func.dead_params.map prod.fst ++ [hd_v],
          --        type := vec_t,
          --        body := eqn_compiler.def_body.term df }
          pure () },
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
                     y ← infer_type e >>= mk_local_def `y,
                     hy ← mk_app `eq [y,e] >>= mk_local_def `hy,
                     let ch_t := (@const tt (func.decl.to_name <.> "child_t" ++ l_name) func.univ_params).mk_app (func.dead_params.map prod.fst ++ [y]),
                     let ch_c := c.update_prefix (func.decl.to_name <.> "child_t" ++ l_name),
                     t ← pis (vs' ++ rec ++ [y,hy]) $ ch_t.imp l.1,
                     (_,f) ← @solve_aux unit t $ do
                       { (vs',σ₀) ← mk_substitution vs' ,
                         (rec,σ₁) ← mk_substitution rec ,
                         y ← intro1, hy ← intro1,
                         x ← intro `x,
                         interactive.generalize `hx () (to_pexpr x,`x'),
                         solve1 $ do
                         { a ← better_induction x,
                           gs ← get_goals,
                           rs ← mzip_with (λ (x : name × list (expr × option expr) × list (name × expr)) g,
                             do let ⟨ctor,a,b⟩ := x,
                                set_goals [g],
                                cases $ hy.instantiate_locals b,
                                gs ← get_goals,
                                pure $ gs.map $ λ g, (a,b,g)) a gs,
                           mzip_with' (λ (v : expr) (r : list (expr × option expr) × list (name × expr) × expr),
                             do let (a,b,g) := r,
                                set_goals [g],
                                x' ← get_local `x',
                                expr.app _ t ← infer_type x',
                                let ts := t.get_app_args.length - func.dead_params.length,
                                let a' := (a.drop ts).map prod.fst, exact $ v.mk_app a' ) vs' rs.join,
                           skip } },
                     pr ← mk_eq_refl e,
                     pure $ f.mk_app $ vs' ++ rec ++ [e,pr] },
          (_,df) ← solve_aux r $ do
            { m ← mk_map_vec func.vec_lvl func.vec_lvl ms,
              refine ``( ⟨ %%e, _ ⟩ ),
              exact m,
              pure () },
          let c' := c.update_prefix $ c.get_prefix <.> "pfunctor",
          let vs := func.params ++ args,
          r  ← pis vs r >>= instantiate_mvars,
          df ← instantiate_mvars df >>= lambdas vs,
          add_decl $ mk_definition c' func.decl.univ_params r df,
          pure () },
   pure ()

-- meta def saturate' : expr → expr → tactic expr
-- | (expr.pi n bi t b) e :=
-- do v ← mk_meta_var t,
--    t ← whnf $ b.instantiate_var v,
--    saturate' t (e v)
-- | t e := pure e

-- meta def saturate (e : expr) : tactic expr :=
-- do t ← infer_type e >>= whnf,
--    saturate' t e

open nat expr

meta def mk_motive : tactic expr :=
do (pi en bi d b) ← target,
   pure $ lam en bi d b

meta def destruct_multimap' : ℕ → expr → expr → list expr → tactic (list expr)
| 0 v₀ v₁ xs :=
do C ← mk_motive,
   refine ``(@typevec_cases_nil₂ %%C _),
   pure xs
| (succ n) v₀ v₁ xs :=
do C ← mk_motive,
   a ← mk_mvar, b ← mk_mvar,
   to_expr ``(append1 %%a %%b) tt ff >>= unify v₀,
   `(append1 %%a' %%b') ← pure v₁,
   refine ``(@typevec_cases_cons₂ _ %%b %%b' %%a %%a' %%C _),
   f ← intro `f,
   destruct_multimap' n a a' (f :: xs)

meta def destruct_multimap (e : expr) : tactic (list expr) :=
do `(%%v₀ ⟹ %%v₁) ← infer_type e,
   `(typevec %%n) ← infer_type v₀,
   n ← eval_expr ℕ n,
   n_h ← revert e,
   destruct_multimap' n v₀ v₁ [] <*
     intron (n_h-1)

def santas_helper {n} {P : mvpfunctor n} {α} (C : P.apply α → Sort*) {a : P.A} {b} (b')
  (x : C ⟨a,b⟩) (h : b = b') : C ⟨a,b'⟩ :=
by cases h; exact x

open list

section zip_vars
variables (n : name) (univs : list level)
  (args : list expr) (shape_args : list expr)

meta def mk_child_arg (e : expr × list expr) : list (expr × expr × ℕ) → list (expr × expr × ℕ) × list expr × expr
| [] := ([],shape_args.tail,shape_args.head)
| (⟨v,e',i⟩::vs) :=
if v.occurs e.1
  then let c : expr := const ( (n.update_prefix $ n.get_prefix ++ v.local_pp_name).append_after i ) univs
       in ( ⟨v,e',i+1⟩::vs, shape_args, expr.lambdas e.2 $ e' $ c.mk_app $ args ++ e.2)
  else prod.map (cons ⟨v,e',i⟩) id $ mk_child_arg vs

meta def zip_vars' : list expr → list (expr × expr × ℕ) → list (expr × list expr) → list expr
| _ xs [] := []
| shape_args xs (v :: vs) :=
let (xs',shape_args',v') := mk_child_arg n univs args shape_args v xs in
v' :: zip_vars' shape_args' xs' vs

meta def zip_vars (ls : list (expr × expr)) (vs : list expr) : tactic $ list expr :=
do vs' ← vs.mmap $ λ v, do { (vs,_) ← infer_type v >>= mk_local_pis, pure (v,vs) },
   pure $ zip_vars' n univs args shape_args (ls.map $ λ x, (x.1,x.2,0)) vs'

end zip_vars

meta def mk_pfunc_recursor (func : internal_mvfunctor) : tactic unit :=
do let u := fresh_univ func.induct.u_names,
   v ← mk_live_vec func.vec_lvl $ func.live_params.map prod.fst,
   fn ← mk_app `mvpfunctor.apply [functor_expr func,v],
   C ← mk_local' `C binder_info.implicit (expr.imp fn $ expr.sort $ level.param u),
   let dead_params := func.dead_params.map prod.fst,
   cases_t ← func.induct.ctors.mmap $ λ c,
   do { let n := c.name.update_prefix (func.decl.to_name <.> "pfunctor"),
        let e := (@expr.const tt n func.induct.u_params).mk_app (func.params ++ c.args),
        prod.mk c <$> (pis c.args (C e) >>= mk_local_def `v) },
   n ← mk_local_def `n fn,
   (_,df) ← solve_aux (expr.pis [n] $ C n) $ do
     { n ← intro1, [(_, [n_fst,n_snd], _)] ← cases_core n,
       hs ← cases_core n_fst,
       gs ← get_goals,
       gs ← list.mzip_with₃ (λ h g v,
         do { let ⟨c,h⟩ := (h : type_cnstr × expr),
              set_goals [g],
              ⟨n,xs,[(_,n_snd)]⟩ ← pure (v : name × list expr × list (name × expr)),
              fs ← destruct_multimap n_snd,
              n_snd ← mk_map_vec func.vec_lvl func.vec_lvl fs,
              let child_n := c.name.update_prefix $ func.induct.name <.> "child_t",
              let subst := (func.live_params.map prod.fst).zip fs,
              h_args ← zip_vars child_n func.induct.u_params (dead_params ++ xs) xs subst c.args,
              let h := h.mk_app h_args,
              let n_fst := (@const tt n func.induct.u_params).mk_app $ func.dead_params.map prod.fst ++ xs,
              vec ← mk_live_vec func.vec_lvl $ func.live_params.map prod.fst,
              fn ← mk_const ``santas_helper,
              unify_mapp fn [none,none,vec,C,none,none,n_snd,h,none] >>= refine ∘ to_pexpr,
              reflexivity <|> (congr; ext [rcases_patt.many [[rcases_patt.one `_]]] none; reflexivity),
              done }) cases_t gs hs,
       pure () },
   let vs := func.params.map expr.to_implicit_binder ++ C :: cases_t.map prod.snd,
   df ← instantiate_mvars df >>= lambdas vs,
   t ← pis (vs ++ [n]) (C n),
   add_decl $ mk_definition (func.pfunctor_name <.> "rec") (u :: func.induct.u_names) t df,
   pure ()

meta def mk_pfunc_rec_eqns (func : internal_mvfunctor) : tactic unit :=
do let u := fresh_univ func.induct.u_names,
   let rec := (@const tt (func.pfunctor_name <.> "rec") (level.param u :: func.induct.u_params)).mk_app func.params,
   let eqn := (@const tt func.eqn_name func.induct.u_params).mk_app func.params,
   (C::fs,_) ← infer_type rec >>= mk_local_pis,
   let rec := rec C,
   let fs := fs.init,
   mzip_with' (λ (c : type_cnstr) (f : expr), do
   { let cn := c.name.update_prefix $ c.name.get_prefix <.> "pfunctor",
     let c := (@const tt cn func.induct.u_params).mk_app func.params,
     (args,_) ← infer_type c >>= mk_local_pis,
     let x := c.mk_app args,
     t ← mk_app `eq [rec.mk_app (fs ++ [x]),f.mk_app args] >>= pis (func.params ++ C :: fs ++ args),
     df ← solve_async [] t $ do
     { intros, reflexivity },
     let n := cn.append_suffix "_rec",
     add_decl $ declaration.thm n (u :: func.induct.u_names) t df,
     simp_attr.typevec.set n () tt }) func.induct.ctors fs,
   skip

meta def mk_qpf_abs (func : internal_mvfunctor) : tactic unit :=
do let n := func.live_params.length,
   let dead_params := func.dead_params.map prod.fst,
   let e := (@const tt func.def_name func.induct.u_params).mk_app dead_params,
   let e' := (@const tt func.pfunctor_name func.induct.u_params).mk_app dead_params,
   t ← to_expr ``(∀ v, mvpfunctor.apply %%e' v → %%e v),
   (_,df) ← @solve_aux unit t $ do
   { vs ← destruct_typevec' func `v,
     C ← mk_motive,
     let params := (rb_map.sort prod.snd $ func.dead_params ++ vs).map prod.fst,
     let rec := @const tt (func.pfunctor_name <.> "rec") $ level.succ func.vec_lvl :: func.induct.u_params,
     let branches := list.repeat (@none expr) func.induct.ctors.length,
     rec ← unify_mapp rec (params.map some ++ C :: branches),
     refine ∘ to_pexpr $ rec,
     let cs := func.induct.ctors,
     let c' := cs.map $ λ c : type_cnstr, c.name.update_prefix $ c.name.get_prefix <.> "pfunctor",
     let eqn := (@const tt func.eqn_name func.induct.u_params).mk_app params,
     cs.mmap $ λ c, solve1 $ do
       { xs ← intros,
         let n := c.name.update_prefix func.induct.name,
         let e := (@const tt n func.induct.u_params).mk_app $ params ++ xs,
         mk_eq_mpr eqn e >>= exact },
     done },
   t ← pis dead_params t,
   df ← instantiate_mvars df >>= lambdas dead_params,
   add_decl $ mk_definition func.abs_name func.induct.u_names t df

meta def mk_qpf_repr (func : internal_mvfunctor) : tactic unit :=
do let n := func.live_params.length,
   let dead_params := func.dead_params.map prod.fst,
   let e := (@const tt func.def_name func.induct.u_params).mk_app dead_params,
   let e' := (@const tt func.pfunctor_name func.induct.u_params).mk_app dead_params,
   t ← to_expr ``(∀ v, %%e v → mvpfunctor.apply %%e' v),
   (_,df) ← @solve_aux unit t $ do
   { vs ← destruct_typevec' func `v,
     C ← mk_motive,
     let params := (rb_map.sort prod.snd $ func.dead_params ++ vs).map prod.fst,
     let rec := @const tt (func.induct.name <.> "rec") $ level.succ func.vec_lvl :: func.induct.u_params,
     let branches := list.repeat (@none expr) func.induct.ctors.length,
     rec ← unify_mapp rec (params.map some ++ C :: branches),
     refine ∘ to_pexpr $ rec,
     let cs := func.induct.ctors,
     let c' := cs.map $ λ c : type_cnstr, c.name.update_prefix $ c.name.get_prefix <.> "pfunctor",
     let eqn := (@const tt func.eqn_name func.induct.u_params).mk_app params,
     cs.mmap $ λ c, solve1 $ do
       { xs ← intros,
         let n := c.name.update_prefix func.pfunctor_name,
         let e := (@const tt n func.induct.u_params).mk_app $ params ++ xs,
         exact e },
     done },
   t ← pis dead_params t,
   df ← instantiate_mvars df >>= lambdas dead_params,
   add_decl $ mk_definition func.repr_name func.induct.u_names t df

open bitraversable

meta def mk_pfunctor_map_eqn (func : internal_mvfunctor) : tactic unit :=
do β ← func.live_params.mmap $ tfst renew,
   fs ← mzip_with (λ x y : expr × _, mk_local_def `f $ x.1.imp y.1) func.live_params β,
   vf ← mk_map_vec func.vec_lvl func.vec_lvl fs,
   let cs := func.induct.ctors.map $ λ c : type_cnstr, c.name.update_prefix func.pfunctor_name,
   let params' := (rb_map.sort prod.snd $ func.dead_params ++ β).map prod.fst,
   cs.mmap' $ λ cn,
     do { let c := (@const tt cn func.induct.u_params).mk_app func.params,
          let c' := (@const tt cn func.induct.u_params).mk_app params',
          (vs,_) ← infer_type c >>= mk_local_pis,
          lhs ← mk_app ``mvfunctor.map [vf,c.mk_app vs],
          vs' ← vs.mmap $ λ v,
            do { some (_,f) ← pure $ ((func.live_params.map prod.fst).zip fs).find $ λ x : expr × expr, x.1.occurs v | pure v,
                 (ws,_) ← infer_type v >>= mk_local_pis,
                 lambdas ws (f $ v.mk_app ws) },
          let rhs := c'.mk_app vs',
          t ← mk_app `eq [lhs,rhs] >>= pis (func.params ++ β.map prod.fst ++ fs ++ vs),
          df ← solve_async [] t $ do
          { intros,
            dunfold_target cs,
            map_eq ← mk_const ``mvpfunctor.map_eq, rewrite_target map_eq { md := semireducible },
            simp_only [``(append_fun_comp'),``(nil_fun_comp)],
            done <|> reflexivity <|> (congr; ext [rcases_patt.many [[rcases_patt.one `_]]] none; reflexivity),
            done },
          let n := cn.append_suffix "_map",
          add_decl $ declaration.thm n func.induct.u_names t df,
          simp_attr.typevec.set n () tt },
   skip

meta def prove_abs_repr (func : internal_mvfunctor) : tactic unit :=
do vs ← destruct_typevec' func `α,
   let cs := func.induct.ctors.map $ λ c : type_cnstr, c.name.update_prefix func.pfunctor_name,
   x ← intro1, cases x,
   repeat $ do
   { dunfold_target [func.repr_name,func.abs_name],
     simp_only [``(typevec.typevec_cases_nil_append1),``(typevec.typevec_cases_cons_append1)],
     dunfold_target $ [func.pfunctor_name <.> "rec"] ++ cs,
     `[dsimp],
     reflexivity }

meta def prove_abs_map (func : internal_mvfunctor) : tactic unit :=
do vs ← destruct_typevec₃ func `α,
   C ← mk_motive,
   let vs := vs.map $ λ ⟨α,β,f,i⟩, (α,i),
   let params := (rb_map.sort prod.snd $ func.dead_params ++ vs).map prod.fst,
   let rec_n := func.pfunctor_name <.> "rec",
   let rec := (@const tt rec_n $ level.zero :: func.induct.u_params).mk_app (params ++ [C]),
   let cs := func.induct.ctors.map $ λ c : type_cnstr, c.name.update_prefix func.pfunctor_name,
   apply rec,
   all_goals $ do
   { intros,
     dunfold_target [func.repr_name,func.abs_name],
     simp_only [``(typevec.typevec_cases_nil_append1),``(typevec.typevec_cases_cons_append1)] [`typevec],
     reflexivity }

meta def mk_mvqpf_instance (func : internal_mvfunctor) : tactic unit :=
do let n := func.live_params.length,
   let dead_params := func.dead_params.map prod.fst,
   let e := (@const tt func.def_name func.induct.u_params).mk_app dead_params,
   let abs_fn := (@const tt func.abs_name func.induct.u_params).mk_app dead_params,
   let repr_fn := (@const tt func.repr_name func.induct.u_params).mk_app dead_params,
   mk_qpf_abs func,
   mk_qpf_repr func,
   mk_pfunctor_map_eqn func,
   pfunctor_i ← mk_mapp ``mvfunctor [some (reflect n),e] >>= mk_instance,
   mvqpf_t ← mk_mapp ``mvqpf [some (reflect n),e,pfunctor_i] >>= instantiate_mvars,
   (_,df) ← solve_aux mvqpf_t $ do
     { let p := (@const tt func.pfunctor_name func.induct.u_params).mk_app dead_params,
       refine ``( { P := %%p, abs := %%abs_fn, repr' := %%repr_fn, .. } ),
       solve1 $ prove_abs_repr func,
       solve1 $ prove_abs_map func },
   df ← instantiate_mvars df >>= lambdas dead_params,
   mvqpf_t ← pis dead_params mvqpf_t,
   let inst_n := func.def_name <.> "mvqpf",
   add_decl $ mk_definition inst_n func.induct.u_names mvqpf_t df,
   set_basic_attribute `instance inst_n

meta def mk_conj : list expr → expr
| [] := `(true)
| [x] := x
| (x :: xs) := @const tt ``and [] x (mk_conj xs)

def list.lookup {α β} [decidable_eq α] (a : α) : list (α × β) → option β
| []             := none
| (⟨a', b⟩ :: l) := if h : a' = a then some b else list.lookup l

meta def replace_all (e : expr) (σ : list (expr × expr)) : expr :=
expr.replace e $ λ x _, list.lookup x σ

meta def mk_liftp_eqns (func : internal_mvfunctor) : tactic unit :=
do let my_t := (@const tt func.induct.name func.induct.u_params).mk_app func.params,
   let F := (@const tt func.def_name func.induct.u_params).mk_app $ func.dead_params.map prod.fst,
   let internal_eq := (@const tt func.eqn_name func.induct.u_params).mk_app func.params,
   x ← mk_local_def `x my_t,
   x' ← mk_eq_mpr internal_eq x,
   let live_params := func.live_params.map prod.fst,
   v ← mk_live_vec func.vec_lvl live_params,
   fs ← live_params.mmap $ λ v, mk_local_def `f $ v.imp `(Prop),
   let m := rb_map.of_list $ list.zip live_params fs,
   fv ← mk_map_vec func.vec_lvl level.zero fs,
   fv_map ← fs.mmap (λ f, mk_mapp ``subtype.val [none,f]) >>= mk_map_vec func.vec_lvl func.vec_lvl,
   fv_t ← fs.mmap (λ f, mk_mapp ``subtype [none,f]) >>= mk_live_vec func.vec_lvl,

   df ← mk_mapp ``typevec.liftp' [none,F,none,v,fv],
   func.induct.ctors.mmap $ λ c, do
   { let e := (@const tt c.name func.induct.u_params).mk_app $ func.params ++ c.args,
     x' ← mk_eq_mpr internal_eq e,
     args ← c.args.mmap $ λ arg, do
       { (args,rhs_t) ← infer_type arg >>= mk_local_pis,
         (some f) ← pure $ m.find rhs_t | pure [],
         list.ret <$> pis args (f $ arg.mk_app args) },
     let rhs := mk_conj args.join,
     t ← pis (c.args.map to_implicit) $ (df x').imp rhs,
     df ← solve_async [func.params,fs] t $ do
     { solve1 $ do
       { args ← intron' c.args.length,
         mk_const ``typevec.liftp_def >>= rewrite_target,
         dunfold_target [``mvfunctor.map],
         h ← intro `h,
         t ← infer_type h,
         let n := func.live_params.length,
         x ← mk_mapp ``subtype_ [`(n),none,fv],
         y ← mk_mapp ``typevec.subtype_val [`(n),none,fv],
         h' ← assertv `h' (replace_all t [(x,fv_t),(y,fv_map)]) h, clear h,
         [(_,[x,y],_)] ← cases_core h',
         hs ← cases_core x,
         gs ← get_goals,
         gs ← (gs.zip hs.enum).mmap $ λ ⟨g,i,n,x,b⟩,
         do { set_goals [g],
              eqn ← mk_const $ (func.induct.name ++ `internal.map._equation).append_after i,
              h' ← rewrite_hyp eqn (y.instantiate_locals b) { md := semireducible },
              t ← target,
              cases h',
              get_goals },
         set_goals gs.join,
         repeat $ do { split, intros, applyc ``subtype.property },
         intros, applyc ``subtype.property <|> interactive.trivial,
         done },
       done },
     t ← pis ((func.params ++ fs).map to_implicit) t,
     add_decl $ declaration.thm (c.name.append_suffix "_liftp") func.induct.u_names t df },
   skip

open interactive lean.parser lean

@[user_command]
meta def qpf_decl (meta_info : decl_meta_info) (_ : parse (tk "qpf")) : parser unit :=
do d ← inductive_decl.parse meta_info,
   func ← mk_internal_functor' d,
   trace_error $ mk_mvfunctor_instance func,
   mk_pfunctor func,
   trace_error $ mk_pfunc_constr func,
   trace_error $ mk_pfunc_recursor func,
   -- trace_error $ mk_pfunc_rec_eqns func,
   -- mk_pfunc_map func,
   -- mk_pfunc_mvfunctor_instance func,
   trace_error $ mk_mvqpf_instance func,
   pure ()

-- local attribute [user_command]  qpf_decl

end tactic
