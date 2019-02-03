
import data.fix.parser.basic
import mvqpf.fix

namespace tactic

open interactive lean lean.parser

meta def foo (n : expr) (v : expr) : type_cnstr → type_cnstr
| (tactic.type_cnstr.mk name args result) :=
{ name := name,
  args := args.map $ λ e, expr.replace e $ λ e' _, if e' = n then pure v else none,
  result := result.map $ λ e, expr.replace e $ λ e' _, if e' = n then pure v else none }

open expr
meta def mk_shape_decl (d : inductive_type) : tactic inductive_type :=
do v ← mk_local_def (fresh_univ (d.params.map expr.local_pp_name) `α) d.type,
   let c := @const tt d.name d.u_params,
   trace d.name.get_prefix,
   trace format!"v: {v}",
   let c' := c.mk_app d.params,
   pure { pre := d.name.get_prefix,
          name := d.name <.> "shape",
          u_names := d.u_names,
          params := d.params ++ [v],
          idx := d.idx,
          type := d.type,
          ctors := d.ctors.map (foo c' v) }

meta def mk_shape_functor' (d : interactive.inductive_decl) : lean.parser (internal_mvfunctor × internal_mvfunctor) :=
do d ← inductive_type.of_decl d,
   func' ← internalize_mvfunctor d,
   func ← mk_shape_decl d,
   mk_inductive' func,
   func ← internalize_mvfunctor func,
   mk_internal_functor_def func,
   mk_internal_functor_eqn func,
   pure (func, func')

meta def mk_fixpoint (func : internal_mvfunctor) (d : internal_mvfunctor) : tactic unit :=
do  let dead := func.dead_params.map prod.fst,
   -- let n := dead.length,
   let shape := (@const tt (func.decl.to_name <.> "internal") func.induct.u_params).mk_app dead,
   trace shape,
   (infer_type shape >>= trace : tactic _),
   -- trace "shape", trace n,
   -- df ← to_expr ``(mvqpf.fix %%shape),
   -- trace "shape",
   df ← (mk_mapp ``mvqpf.fix [none,shape,none,none] >>= lambdas dead : tactic _),
   -- trace "shape",
   t ← infer_type df,
   let intl_n := func.decl.to_name.get_prefix <.> "internal",
   add_decl $ mk_definition intl_n func.induct.u_names t df,
   v ← mk_live_vec func.vec_lvl $ func.live_params.init.map prod.fst,
   df ← lambdas d.params $ (@const tt intl_n func.induct.u_params).mk_app (d.dead_params.map prod.fst ++ [v]),
   t  ← infer_type df,
   add_decl $ mk_definition func.decl.to_name.get_prefix func.induct.u_names t df

@[user_command]
meta def data_decl (meta_info : decl_meta_info) (_ : parse (tk "data")) : parser unit :=
do d ← inductive_decl.parse meta_info,
   (func, d) ← mk_shape_functor' d,
   mk_mvfunctor_instance func,
   mk_pfunctor func,
   mk_pfunc_constr func,
   mk_pfunc_recursor func,
   -- mk_pfunc_map func,
   -- mk_pfunc_mvfunctor_instance func,
   mk_mvqpf_instance func,
   mk_fixpoint func d,
   pure ()

end tactic

data nat'
| zero : nat'
| succ : nat' → nat'

#print nat'.internal
#print nat'

universes u
namespace hidden

set_option trace.app_builder true
data list (α : Type u) : Type u
| zero : list
| succ : α → list → list

#print hidden.list.internal
#print hidden.list

end hidden

-- list
-- tree
-- infinitary tree
