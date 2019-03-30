
import data.fix.parser.basic
import mvqpf.fix
import mvqpf.cofix

namespace tactic

open interactive lean lean.parser

meta def foo (n : expr) (v : expr) : type_cnstr → type_cnstr
| (tactic.type_cnstr.mk name args result) :=
{ name := name,
  args := args.map $ λ e, expr.replace e $ λ e' _, if e' = n then pure v else none,
  result := result.map $ λ e, expr.replace e $ λ e' _, if e' = n then pure v else none }

open expr interactive

meta structure datatype_shape extends internal_mvfunctor :=
(hole : expr)

meta def mk_shape_decl (d : inductive_type) : tactic (expr × inductive_type) :=
do v ← mk_local_def (fresh_univ (d.params.map expr.local_pp_name) `α) d.type,
   let c := @const tt d.name d.u_params,
   let c' := c.mk_app d.params,
   pure (v, { pre := d.name.get_prefix,
              name := d.name <.> "shape",
              u_names := d.u_names,
              params := d.params ++ [v],
              idx := d.idx,
              type := d.type,
              ctors := d.ctors.map (foo c' v) })

meta def mk_shape_functor' (d : interactive.inductive_decl) : lean.parser (datatype_shape × internal_mvfunctor) :=
do d ← inductive_type.of_decl d,
   func' ← internalize_mvfunctor d,
   (v,func) ← mk_shape_decl d,
   mk_inductive' func,
   func ← internalize_mvfunctor func,
   mk_internal_functor_def func,
   mk_internal_functor_eqn func,
   pure ({ hole := v .. func }, func')

meta def decl_kind : declaration → string
| (declaration.defn a a_1 a_2 a_3 a_4 a_5) := "defn"
| (declaration.thm a a_1 a_2 a_3) := "thm"
| (declaration.cnst a a_1 a_2 a_3) := "cnst"
| (declaration.ax a a_1 a_2) := "ax"


meta def mk_fixpoint (fix : name) (func d : internal_mvfunctor) : tactic unit :=
do let dead := func.dead_params.map prod.fst,
   let shape := (@const tt (func.decl.to_name <.> "internal") func.induct.u_params).mk_app dead,
   df ← (mk_mapp fix [none,shape,none,none] >>= lambdas dead : tactic _),
   t ← infer_type df,
   let intl_n := func.decl.to_name.get_prefix <.> "internal",
   add_decl $ mk_definition intl_n func.induct.u_names t df,
   v ← mk_live_vec func.vec_lvl $ func.live_params.init.map prod.fst,
   df ← lambdas d.params $ (@const tt intl_n func.induct.u_params).mk_app (func.dead_params.map prod.fst ++ [v]),
   t  ← infer_type df,
   add_decl $ mk_definition func.decl.to_name.get_prefix func.induct.u_names t df,
   pure ()

meta def mk_datatype (iter : name) (d : inductive_decl) : parser (datatype_shape × internal_mvfunctor) :=
do (func', d) ← mk_shape_functor' d,
   let func : internal_mvfunctor := { .. func' },
   mk_mvfunctor_instance func,
   mk_pfunctor func,
   mk_pfunc_constr func,
   mk_pfunc_recursor func,
   mk_mvqpf_instance func,
   mk_fixpoint iter func d,
   pure (func',d)

end tactic
