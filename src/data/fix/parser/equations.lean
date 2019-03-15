import data.fix.parser.shape

namespace tactic

open interactive lean lean.parser
open expr

#check mvqpf.cofix.dest
#check mvqpf.cofix.mk

meta def mk_constr (mk_fn : name) (d : internal_mvfunctor) : tactic unit :=
do let my_t := (@const tt d.induct.name d.induct.u_params).mk_app d.params,
   let intl_eq := (@const tt (d.induct.name <.> "shape" <.> "internal_eq") d.induct.u_params).mk_app (d.params ++ [my_t]),
   d.induct.ctors.mmap' $ λ c : type_cnstr,
     do { t ← type_cnstr.type d.induct c,
          let t := instantiate_pi t d.params,
          let c' := c.name.update_prefix (d.decl.to_name <.> "shape"),
          (vs,t') ← mk_local_pis t,
          let mk_shape := (@const tt c' d.induct.u_params).mk_app (d.params ++ [my_t] ++ vs),
          e ← mk_eq_mpr intl_eq mk_shape,
          df ← mk_app mk_fn [e] >>= lambdas (d.params ++ vs),
          t ← pis d.params t,
          add_decl $ mk_definition c.name d.induct.u_names t df }

meta def mk_corecursor (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
do let u := fresh_univ d.induct.u_names,
   let t := (@const tt d.decl.to_name d.induct.u_params).mk_app d.params,
   let x := func.hole,
   v ← mk_live_vec d.vec_lvl $ d.live_params.map prod.fst,
   v' ← mk_live_vec d.vec_lvl $ x :: d.live_params.map prod.fst,
   let u_params := d.induct.u_params,
   let n := d.decl.to_name,
   let shape_n := n <.> "shape",
   let internal_eq_n := shape_n <.> "internal_eq",
   let t' := (@const tt (shape_n <.> "internal") d.induct.u_params), -- .mk_app [v'],
   let ft := imp x $ (@const tt shape_n u_params).mk_app $ func.params,
   let intl_eq := (@const tt internal_eq_n u_params).mk_app $ d.params,
   fn ← mk_local_def `f ft,
   i ← mk_local_def `i x,
   fn' ← mk_eq_mpr (intl_eq x) (fn i) >>= lambdas [i],
   df' ← mk_mapp ``mvqpf.cofix.corec [none,t',none,none,v,x],
   df ← mk_mapp ``mvqpf.cofix.corec [none,t',none,none,v,x,fn'],
   let t := imp x $ (@const tt n u_params).mk_app d.params,
   t ← pis (d.params ++ [x,fn]) t,
   df ← lambdas (d.params ++ [x,fn]) df,
   add_decl $ mk_definition (n <.> "corec") (u :: d.induct.u_names) t df,
   pure ()

@[user_command]
meta def data_decl (meta_info : decl_meta_info) (_ : parse (tk "data")) : parser unit :=
do d ← inductive_decl.parse meta_info,
   (func,d) ← mk_datatype ``mvqpf.fix d,
   trace_error $ mk_constr ``mvqpf.fix.mk d,
   pure ()

@[user_command]
meta def codata_decl (meta_info : decl_meta_info) (_ : parse (tk "codata")) : parser unit :=
do d ← inductive_decl.parse meta_info,
   (func,d) ← mk_datatype ``mvqpf.cofix d,
   trace_error $ mk_constr ``mvqpf.cofix.mk d,
   trace_error $ mk_corecursor func d,
   pure ()

end tactic

data nat'
| zero : nat'
| succ : nat' → nat'

#print nat'.zero
#print nat'.succ

codata nat''
| zero : nat''
| succ : nat'' → nat''

-- -- #print nat'.internal
-- #print prefix nat''.corec
#print nat''.zero
#print nat''.succ

universes u
namespace hidden

data list (α : Type u) : Type u
| zero : list
| succ : α → list → list

-- #print hidden.list.internal
-- #print hidden.list
-- set_option trace.app_builder true
-- set_option debugger true

-- local attribute [vm_monitor] stack_trace

codata stream (α : Type u) : Type u
| zero : stream
| succ : α → stream → stream

#print hidden.stream.internal
#print hidden.stream
#print hidden.stream.corec
#print hidden.stream.zero
#print hidden.stream.succ

codata stream' (α : Type u) : Type u
| zero : stream'
| succ : α → (ℤ → stream') → stream'

#print hidden.stream'.internal
#print hidden.stream'
#check hidden.stream'.zero
#check @hidden.stream'.succ
#print hidden.stream'.shape
#print hidden.stream'.corec
#print hidden.stream'.zero
#print hidden.stream'.succ

-- codata stream₁ (α : Type u) : Type u
-- | zero : stream₁
-- | succ : α → (list stream₁) → stream₁

-- #print hidden.stream₁.internal
-- #print hidden.stream₁
-- #print hidden.stream₁.shape
-- #print hidden.stream₁.corec

end hidden
