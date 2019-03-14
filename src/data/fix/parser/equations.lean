import data.fix.parser.shape

namespace tactic

open interactive lean lean.parser

meta def mk_constr (d : internal_mvfunctor) : tactic unit :=
do d.induct.ctors.mmap' $ λ c : type_cnstr,
     do { t ← type_cnstr.type d.induct c >>= pis d.params ,
          trace format!"{c.name} : {t}",
          let df := t.mk_sorry,
          add_decl $ mk_definition c.name d.induct.u_names t df }

open expr

meta def mk_corecursor (d : internal_mvfunctor) : tactic unit :=
do let u := fresh_univ d.induct.u_names,
   let t := (@const tt d.decl.to_name d.induct.u_params).mk_app d.params,
   -- trace "→ infer_type ←",
   -- infer_type t' >>= trace,
   x ← mk_local' `α' binder_info.implicit $ sort (level.succ d.vec_lvl),
   v ← mk_live_vec d.vec_lvl $ d.live_params.map prod.fst,
   v' ← mk_live_vec d.vec_lvl $ x :: d.live_params.map prod.fst,
   infer_type v' >>= trace,
   -- infer_type x >>= trace,
   let u_params := d.induct.u_params,
   let n := d.decl.to_name,
   let shape_n := n <.> "shape",
   let internal_eq_n := shape_n <.> "internal_eq",
   let t' := (@const tt (shape_n <.> "internal") d.induct.u_params), -- .mk_app [v'],
   let ft := imp x $ (@const tt shape_n u_params).mk_app $ d.params ++ [x],
   -- let ft := imp x $ (@const tt shape_n u_params).mk_app $ x :: d.params,
   let intl_eq := (@const tt internal_eq_n u_params).mk_app $ d.params,
   trace "== LET ==",
   infer_type (@const tt shape_n u_params) >>= trace,
   infer_type intl_eq >>= trace,
   trace format!"ft: {ft}",
   trace format!"t': {t'}",
   infer_type t' >>= trace,
   trace "== end traces ==",
   fn ← mk_local_def `f ft,
   i ← mk_local_def `i x,
   fn' ← mk_eq_mpr (intl_eq x) (fn i) >>= lambdas [i],
   trace " *** ",
   -- mk_const ``mvqpf.cofix.corec >>= infer_type >>= trace,
   infer_type fn' >>= trace,
   df' ← mk_mapp ``mvqpf.cofix.corec [none,t',none,none],
   infer_type df' >>= trace,
   df ← mk_mapp ``mvqpf.cofix.corec [none,t',none,none,v,x,fn'],
   -- let n := (d.decl.to_name <.> "shape" <.> "internal"),
   -- trace n,
   -- d ← get_decl n, trace d.type, trace $ decl_kind d, trace d.value,
   trace " *** ",
   -- trace df,
   -- t' ← infer_type df, trace t',
   let t := imp x $ (@const tt n u_params).mk_app d.params,
   t ← pis (d.params ++ [x,fn]) t, trace t,
   df ← lambdas (d.params ++ [x,fn]) df,
   add_decl $ mk_definition (n <.> "corec") (u :: d.induct.u_names) t df,
   -- C ← mk_local' `C binder_info.implicit (sort $ level.succ $ level.param u),
   -- infer_type C >>= trace, trace "foo",
   pure ()

-- nat''.shape.internal_eq : ∀ (α_1 : Type), nat''.shape.internal ⦃ α_1 ⦄ = shape α_1

@[user_command]
meta def data_decl (meta_info : decl_meta_info) (_ : parse (tk "data")) : parser unit :=
do d ← inductive_decl.parse meta_info,
   d ← mk_datatype ``mvqpf.fix d,
   trace_error $ mk_constr d,
   pure ()

@[user_command]
meta def codata_decl (meta_info : decl_meta_info) (_ : parse (tk "codata")) : parser unit :=
do d ← inductive_decl.parse meta_info,
   d ← mk_datatype ``mvqpf.cofix d,
   trace_error $ mk_constr d,
   trace_error $ mk_corecursor d,
   pure ()

end tactic


-- data nat'
-- | zero : nat'
-- | succ : nat' → nat'
codata nat''
| zero : nat''
| succ : nat'' → nat''

-- -- #print nat'.internal
#print prefix nat''.corec

universes u
namespace hidden

-- data list (α : Type u) : Type u
-- | zero : list
-- | succ : α → list → list

-- #print hidden.list.internal
-- #print hidden.list
set_option trace.app_builder true

-- codata stream (α : Type u) : Type u
-- | zero : stream
-- | succ : α → stream → stream

-- #print hidden.stream.internal
-- #print hidden.stream

end hidden
