import data.fix.parser.shape

namespace tactic

open interactive lean lean.parser
open expr

meta def trace' {α} (x : α) [has_to_tactic_format α] : tactic α :=
x <$ trace x

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

meta def mk_destr (dest_fn mk_fn mk_dest_eqn : name) (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
do let params := d.params.map to_implicit,
   let my_t := (@const tt d.induct.name d.induct.u_params).mk_app params,
   vec ← mk_live_vec d.vec_lvl (d.live_params.map prod.fst ++ [my_t]),
   vec' ← mk_live_vec d.vec_lvl (d.live_params.map prod.fst),
   let my_shape_t := (@const tt (d.induct.name <.> "shape" <.> "internal") d.induct.u_params).mk_app (func.dead_params.map prod.fst),
   let u_params := d.induct.u_params,
   let u := fresh_univ d.induct.u_names,
   let intl_eq := (@const tt (d.induct.name <.> "shape" <.> "internal_eq") u_params).mk_app (params ++ [my_t]),
   v_t ← mk_local_def `x (my_shape_t vec),
   C ← mk_local' `C binder_info.implicit (my_t.imp (sort $ level.param u)),
   let n := d.live_params.length,
   C' ← mk_mapp mk_fn [reflect n,my_shape_t,none,none,vec',v_t] >>= lambdas [v_t] ∘ C,
   cs ← d.induct.ctors.mmap $ λ c : type_cnstr,
     do { let t := (@const tt c.name u_params).mk_app params ,
          (vs,_) ← infer_type t >>= mk_local_pis,
          x ← pis vs (C $ t.mk_app vs),
          v ← mk_local_def `v x,
          pure (v) },
   n ← mk_local_def `n my_t,
   n' ← mk_app dest_fn [n],
   let vs := params ++ [C,n] ++ cs,
   rec_t ← pis vs (C n),
   let shape_cases := (@const tt (d.induct.name <.> "shape" <.> "cases_on") $ level.param u :: u_params).mk_app (params ++ [my_t,C',n'] ++ cs),
   shape_cases ← mk_app mk_dest_eqn [n] >>= mk_congr_arg C >>= flip mk_eq_mp shape_cases,
   df ← lambdas vs shape_cases,
   add_decl $ mk_definition (d.induct.name <.> "cases_on") (u :: d.induct.u_names) rec_t df,
   pure ()

open tactic.interactive (rw_rules_t rw_rule)
open tactic.interactive.rw_rules_t
open interactive.rw_rule

meta def mk_dep_recursor (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
do let params := d.params.map to_implicit,
   let my_shape_intl_t := (@const tt (d.induct.name <.> "shape" <.> "internal") d.induct.u_params).mk_app (func.dead_params.map prod.fst),
   let u_params := d.induct.u_params,
   vec' ← mk_live_vec d.vec_lvl (d.live_params.map prod.fst),
   arg ← mk_local_def `y ((@const tt d.induct.name d.induct.u_params).mk_app params),
   C ← pis [arg] d.type >>= mk_local' `C binder_info.implicit,
   X ← mk_app ``sigma [C],
   vec ← mk_live_vec d.vec_lvl (d.live_params.map prod.fst ++ [X]),
   let my_shape_t := (@const tt (d.induct.name <.> "shape") d.induct.u_params).mk_app (params ++ [X]),
   v_t ← mk_local_def `x my_shape_t,
   x ← mk_local_def `x' (my_shape_intl_t vec),
   let intl_eq := (@const tt (d.induct.name <.> "shape" <.> "internal_eq") u_params).mk_app (params ++ [X]),
   x' ← mk_eq_mpr intl_eq x,
   C' ← to_expr ``(%%C $ mvqpf.fix.mk (typevec.append_fun typevec.id sigma.fst <$$> %%x')) >>= lambdas [x],
   let cases_on := d.induct.name <.> "shape" <.> "cases_on",
   let cases_u : list level := level.succ d.vec_lvl :: d.induct.u_params,
   let fs := (@const tt cases_on cases_u).mk_app $ params ++ [X,C',x'],
   (vs,_) ← infer_type fs >>= mk_local_pis,
   vs ← mzip_with (λ l (c : type_cnstr),
     do { (args,t) ← infer_type l >>= mk_local_pis,
          head_beta t >>= pis args >>= mk_local_def l.local_pp_name }) vs d.induct.ctors,
   let fn := fs.mk_app vs,
   rule ← mk_const ``mpr_mpr,
   (t',pr,_) ← infer_type fn >>= head_beta >>= rewrite rule,
   fn ← mk_eq_mp pr fn >>= lambdas [x],
   df ← mk_mapp ``mvqpf.fix.drec [none,my_shape_intl_t,none,none,vec',C,fn,arg]
     >>= lambdas (params ++ C :: vs ++ [arg]),
   t ← infer_type df,
   add_decl $ mk_definition (d.induct.name <.> "drec") d.induct.u_names t df,
   pure ()

meta def mk_recursor (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
do let my_shape_intl_t := (@const tt (d.induct.name <.> "shape" <.> "internal") d.induct.u_params).mk_app (func.dead_params.map prod.fst),
   let my_shape_t := (@const tt (d.induct.name <.> "shape") d.induct.u_params).mk_app func.params,
   let u_params := d.induct.u_params,
   let X := to_implicit func.hole,
   let intl_eq := (@const tt (d.induct.name <.> "shape" <.> "internal_eq") u_params).mk_app (d.params ++ [X]),
   vec' ← mk_live_vec d.vec_lvl (d.live_params.map prod.fst),
   vec ← mk_live_vec d.vec_lvl (d.live_params.map prod.fst ++ [X]),
   x ← mk_local_def `x (my_shape_intl_t vec),
   v_t ← mk_local_def `x my_shape_t,
   C ← lambdas [v_t] X,
   v_t ← mk_eq_mp intl_eq x,
   let cases_on := d.induct.name <.> "shape" <.> "cases_on",
   let cases_u : list level := level.succ d.vec_lvl :: d.induct.u_params,
   let fs := (@const tt cases_on $ cases_u).mk_app $ func.params ++ [C,v_t],
   (vs,_) ← infer_type fs >>= mk_local_pis,
   vs ← mzip_with (λ l (c : type_cnstr),
     do { (args,t) ← infer_type l >>= mk_local_pis,
          head_beta t >>= pis args >>= mk_local_def l.local_pp_name }) vs d.induct.ctors,
   fn ← lambdas [x] (fs.mk_app vs),
   arg ← mk_local_def `y $ (@const tt d.induct.name d.induct.u_params).mk_app d.params,
   let params := d.params.map to_implicit,
   df ← mk_mapp ``mvqpf.fix.rec [none,my_shape_intl_t,none,none,vec',X,fn,arg] >>= lambdas (params ++ X :: vs ++ [arg]),
   t ← infer_type df,
   add_decl $ mk_definition (d.induct.name <.> "rec") d.induct.u_names t df,
   pure ()

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
   let t' := (@const tt (shape_n <.> "internal") d.induct.u_params).mk_app $ func.dead_params.map prod.fst,
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

meta def mk_datatype' (iter : name) (d : inductive_decl) : parser (datatype_shape × internal_mvfunctor) :=
do (func', d) ← mk_shape_functor' d,
   let func : internal_mvfunctor := { .. func' },
   mk_mvfunctor_instance func,
   trace "• A •",
   mk_pfunctor func,
   trace "• A •",
   mk_pfunc_constr func,
   trace "• A •",
   mk_pfunc_recursor func,
   mk_mvqpf_instance func,
   mk_fixpoint iter func d,
   pure (func',d)

@[user_command]
meta def data_decl (meta_info : decl_meta_info) (_ : parse (tk "data")) : parser unit :=
do d ← inductive_decl.parse meta_info,
   (func,d) ← mk_datatype' ``mvqpf.fix d,
   trace_error $ mk_constr ``mvqpf.fix.mk d,
   trace_error $ mk_destr ``mvqpf.fix.dest ``mvqpf.fix.mk ``mvqpf.fix.mk_dest func d,
   trace_error $ mk_recursor func d,
   trace_error $ mk_dep_recursor func d,
   pure ()

@[user_command]
meta def codata_decl (meta_info : decl_meta_info) (_ : parse (tk "codata")) : parser unit :=
do d ← inductive_decl.parse meta_info,
   (func,d) ← mk_datatype ``mvqpf.cofix d,
   trace_error $ mk_constr ``mvqpf.cofix.mk d,
   trace_error $ mk_destr ``mvqpf.cofix.dest ``mvqpf.cofix.mk ``mvqpf.cofix.mk_dest func d,
   trace_error $ mk_corecursor func d,
   pure ()

end tactic

universes u

data list' (γ α β γ' : Type u) : Type u
| zero : γ → list'
| succ : γ' → α → (ℤ → β → list') → list'

#check list'.drec
#print list'.shape.internal.map

data nat'
| zero : nat'
| succ : nat' → nat'

#check nat'.drec
#print nat'.zero
#print nat'.succ

codata nat''
| zero : nat''
| succ : nat'' → nat''

-- -- #print nat'.internal
-- #print prefix nat''.corec
#print nat''.zero
#print nat''.succ

namespace hidden

data list (α : Type u) : Type u
| nil : list
| cons : α → list → list

#print hidden.list.internal
#print hidden.list
#print hidden.list.rec
#check @hidden.list.drec

codata stream (α : Type u) : Type u
| zero : stream
| succ : α → stream → stream

#print hidden.stream.internal
#print hidden.stream
#print hidden.stream.cases_on
#print hidden.stream.corec
#print hidden.stream.zero
#print hidden.stream.succ

codata stream' (γ α β γ' : Type u) : Type u
| zero : γ → stream'
| succ : γ' → α → (ℤ → β → stream') → stream'

#print hidden.stream'.internal
#print hidden.stream'
#check hidden.stream'.zero
#print hidden.stream'.cases_on
#check @hidden.stream'.succ
#print hidden.stream'.shape
#print hidden.stream'.corec
#print hidden.stream'.zero
#print hidden.stream'.succ

-- data list'' (α β : Type) : Type
-- | nil : list''
-- | cons : α → α → (β → list'') → list''

data list' (γ α β γ' : Type u) : Type u
| zero : γ → list'
| succ : γ' → α → (ℤ → β → list') → list'

#print hidden.list'.rec

data list'' (α β : Type) : Type
| nil : list''
| cons : α → (β → list'') → list''

-- -- Shape functor
-- inductive list.shape (α : Type) (β : Type) (X : Type) : Type
-- | nil : list.shape
-- | cons : α → (β → X) → list.shape

-- inductive list.shape.head_t (β : Type) : Type
-- | nil : list.shape.head_t
-- | cons : list.shape.head_t

-- inductive list.shape.child_t.α (β : Type) : list.shape.head_t β → Type
-- | cons_0 : list.shape.child_t.α (list.shape.head_t.cons β)

-- inductive list.shape.child_t.X (β : Type) : list.shape.head_t β → Type
-- | cons_0 : β → list.shape.child_t.X (list.shape.head_t.cons β)

#print hidden.list''.shape.child_t
-- def list.shape.child_t (β : Type) (hd : head_t β) : typevec 2 := ⦃ child_t.X β hd, child_t.α β hd ⦄

#print list''.shape.pfunctor
-- def list.shape.pfunctor (β : Type) : mvpfunctor 2 := {A := head_t β, B := child_t β}

#print list''.shape.internal
-- def list.shape.internal (β : Type) : typevec 2 → Type
-- | ⟨α,X,_⟩ := shape α β X

-- instance (β : Type) : mvfunctor (list.shape.internal β) := ...
-- instance (β : Type) : mvqpf (list.shape.internal β) := ...

-- def list.internal (β : Type) (v : typevec 1) : Type := fix (list.shape.internal β) v
-- def list (α β : Type) : Type := list.internal β ⦃ α ⦄

-- instance (β : Type) : mvfunctor (list.internal β) := ...
-- instance (β : Type) : mvqpf (list.internal β) := ...

-- -- Constructors
#print list''.nil
-- def list.nil (α β : Type) : list α β := ...

#print list''.cons
-- def list.cons (α β : Type) (x : α) (xs : β → list α β) : list α β := ...

-- -- Destructor
#print list''.cases_on
-- def list.cases_on {α β : Type} {C : list α β → Sort u_1} (n : list α β) :
--   C (list.nil α β) →
--   (Π (a : α) (a_1 : β → list α β), C (list.cons α β a a_1)) →
--   C n := ...

-- recursors
#print list''.rec
-- def list.rec {α β X : Type} : X → (α → (β → X) → X) → list α β → X := ...

#print list''.drec
-- def list.drec {α β : Type} {C : list α β → Sort u_1} :
--   C (list.nil α β) →
--   (Π (x : α) (xs : β → list α β), (Π i : β, C (xs i)) → C (list.cons α β x xs)) →
--   Π (n : list α β), C n := ...

-- codata stream₁ (α : Type u) : Type u
-- | zero : stream₁
-- | succ : α → (list stream₁) → stream₁

-- #print hidden.stream₁.internal
-- #print hidden.stream₁
-- #print hidden.stream₁.shape
-- #print hidden.stream₁.corec

end hidden
