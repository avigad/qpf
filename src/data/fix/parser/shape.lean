
import data.fix.parser.basic
import mvqpf.fix
import mvqpf.cofix

namespace tactic

open interactive lean lean.parser

meta def replace_rec_occ (tn tn' : name) (nested : expr) (var : expr) : type_cnstr → type_cnstr
| (tactic.type_cnstr.mk name args result infer) :=
{ name := name.replace_prefix tn tn',
  args := args.map $ λ e, expr.replace e $ λ e' _, if e' = nested then pure var else none,
  result := result.map $ λ e, expr.replace e $ λ e' _, if e' = nested then pure var else none,
  infer := infer }

open expr interactive

meta structure datatype_shape extends internal_mvfunctor :=
(hole : expr)

meta def datatype_shape.params (d : datatype_shape) := internal_mvfunctor.params d.to_internal_mvfunctor
meta def datatype_shape.dead_params (d : datatype_shape) := internal_mvfunctor.dead_params d.to_internal_mvfunctor
meta def datatype_shape.live_params (d : datatype_shape) := internal_mvfunctor.live_params d.to_internal_mvfunctor

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
              ctors := d.ctors.map (replace_rec_occ d.name (d.name <.> "shape") c' v) })

meta def mk_shape_functor' (d : interactive.inductive_decl) : tactic (datatype_shape × internal_mvfunctor) :=
do d ← inductive_type.of_decl d,
   func' ← internalize_mvfunctor d,
   (v,func) ← mk_shape_decl d,
   mk_inductive func,
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
do let dead := func.dead_params,
   let shape := (@const tt (func.decl.to_name <.> "internal") func.induct.u_params).mk_app dead,
   df ← (mk_mapp fix [none,shape,none,none] >>= lambdas dead : tactic _),
   t ← infer_type df,
   let intl_n := func.decl.to_name.get_prefix <.> "internal",
   add_decl $ mk_definition intl_n func.induct.u_names t df,
   v ← mk_live_vec func.vec_lvl $ func.live_params.init,
   df ← lambdas d.params $ (@const tt intl_n func.induct.u_params).mk_app func.dead_params v,
   t  ← infer_type df,
   add_decl $ mk_definition func.decl.to_name.get_prefix func.induct.u_names t df,
   pure ()

meta def timetac' {α : Type*} (_ : string) (tac : thunk (tactic α)) : tactic α :=
tac ()

meta def mk_datatype (iter : name) (d : inductive_decl) : tactic (datatype_shape × internal_mvfunctor) :=
do (func', d) ← mk_shape_functor' d,
   let func : internal_mvfunctor := { .. func' },
   timetac' "mk_mvfunctor_instance" $ mk_mvfunctor_instance func,
   mk_pfunctor func,
   timetac' "mk_pfunc_constr" $ mk_pfunc_constr func,
   timetac' "mk_pfunc_recursor" $ mk_pfunc_recursor func,
   timetac' "mk_mvqpf_instance" $ mk_mvqpf_instance func,
   timetac' "mk_fixpoint" $ mk_fixpoint iter func d,
   mk_liftp_defn' func,
   mk_liftp_eqns₀ func,
   mk_liftp_eqns₁ func,
   mk_liftr_defn' func,
   mk_liftr_eqns₀ func,
   mk_liftr_eqns₁ func,
   pure (func',d)

end tactic
