import data.fix.parser.shape
import category.bitraversable.lemmas
import category.bitraversable.instances

namespace tactic

open interactive lean lean.parser
open expr

meta def trace' {α} (x : α) [has_to_tactic_format α] : tactic α :=
x <$ trace x

meta def mk_constr (mk_fn : name) (d : internal_mvfunctor) : tactic unit :=
do let my_t := (@const tt d.induct.name d.induct.u_params).mk_app d.params,
   let intl_eq := (@const tt (d.induct.name <.> "shape" <.> "internal_eq") d.induct.u_params).mk_app (d.params ++ [my_t]),
   let params := d.params.map to_implicit,
   d.induct.ctors.mmap' $ λ c : type_cnstr,
     do { t ← type_cnstr.type d.induct c,
          let t := instantiate_pi t params,
          let c' := c.name.update_prefix (d.decl.to_name <.> "shape"),
          (vs,t') ← mk_local_pis t,
          let mk_shape := (@const tt c' d.induct.u_params).mk_app (params ++ [my_t] ++ vs),
          e ← mk_eq_mpr intl_eq mk_shape,
          df ← mk_app mk_fn [e] >>= lambdas (params ++ vs),
          t ← pis params t,
          add_decl $ mk_definition c.name d.induct.u_names t df }

meta def mk_destr (dest_fn mk_fn mk_dest_eqn : name) (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
do let my_t := (@const tt d.induct.name d.induct.u_params).mk_app d.params,
   vec ← mk_live_vec d.vec_lvl (d.live_params.map prod.fst ++ [my_t]),
   vec' ← mk_live_vec d.vec_lvl (d.live_params.map prod.fst),
   let my_shape_t := (@const tt (d.induct.name <.> "shape" <.> "internal") d.induct.u_params).mk_app (func.dead_params.map prod.fst),
   let u_params := d.induct.u_params,
   let u := fresh_univ d.induct.u_names,
   let intl_eq := (@const tt (d.induct.name <.> "shape" <.> "internal_eq") u_params).mk_app (d.params ++ [my_t]),
   v_t ← mk_local_def `x (my_shape_t vec),
   C ← mk_local' `C binder_info.implicit (my_t.imp (sort $ level.param u)),
   let n := d.live_params.length,
   C' ← mk_mapp mk_fn [reflect n,my_shape_t,none,none,vec',v_t] >>= lambdas [v_t] ∘ C,
   cs ← d.induct.ctors.mmap $ λ c : type_cnstr,
     do { let t := (@const tt c.name u_params).mk_app d.params ,
          (vs,_) ← infer_type t >>= mk_local_pis,
          x ← pis vs (C $ t.mk_app vs),
          v ← mk_local_def `v x,
          pure (v) },
   n ← mk_local_def `n my_t,
   n' ← mk_app dest_fn [n],
   let vs := d.params ++ [C,n] ++ cs,
   rec_t ← pis vs (C n),
   let shape_cases := (@const tt (d.induct.name <.> "shape" <.> "cases_on") $ level.param u :: u_params).mk_app (d.params ++ [my_t,C',n'] ++ cs),
   shape_cases ← mk_app mk_dest_eqn [n] >>= mk_congr_arg C >>= flip mk_eq_mp shape_cases,
   df ← lambdas vs shape_cases,
   add_decl $ mk_definition (d.induct.name <.> "cases_on") (u :: d.induct.u_names) rec_t df,
   pure ()

open tactic.interactive (rw_rules_t rw_rule)
open tactic.interactive.rw_rules_t
open interactive.rw_rule

meta def mk_dep_recursor (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
do let my_shape_intl_t := (@const tt (d.induct.name <.> "shape" <.> "internal") d.induct.u_params).mk_app (func.dead_params.map prod.fst),
   let u_params := d.induct.u_params,
   vec' ← mk_live_vec d.vec_lvl (d.live_params.map prod.fst),
   arg ← mk_local_def `y ((@const tt d.induct.name d.induct.u_params).mk_app d.params),
   C ← pis [arg] d.type >>= mk_local' `C binder_info.implicit,
   X ← mk_app ``sigma [C],
   vec ← mk_live_vec d.vec_lvl (d.live_params.map prod.fst ++ [X]),
   let my_shape_t := (@const tt (d.induct.name <.> "shape") d.induct.u_params).mk_app (d.params ++ [X]),
   v_t ← mk_local_def `x my_shape_t,
   x ← mk_local_def `x' (my_shape_intl_t vec),
   let intl_eq := (@const tt (d.induct.name <.> "shape" <.> "internal_eq") u_params).mk_app (d.params ++ [X]),
   x' ← mk_eq_mpr intl_eq x,
   C' ← to_expr ``(%%C $ mvqpf.fix.mk (typevec.append_fun typevec.id sigma.fst <$$> %%x')) >>= lambdas [x],
   let cases_on := d.induct.name <.> "shape" <.> "cases_on",
   let cases_u : list level := level.succ d.vec_lvl :: d.induct.u_params,
   let fs := (@const tt cases_on cases_u).mk_app $ d.params ++ [X,C',x'],
   (vs,_) ← infer_type fs >>= mk_local_pis,
   vs ← mzip_with (λ l (c : type_cnstr),
     do { (args,t) ← infer_type l >>= mk_local_pis,
          head_beta t >>= pis args >>= mk_local_def l.local_pp_name }) vs d.induct.ctors,
   let fn := fs.mk_app vs,
   rule ← mk_const ``mpr_mpr,
   (t',pr,_) ← infer_type fn >>= head_beta >>= rewrite rule,
   fn ← mk_eq_mp pr fn >>= lambdas [x],
   let params := d.params.map to_implicit,
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

open add_coinductive_predicate
private meta def compact_relation :
  list expr → list (expr × expr) → list expr × list (expr × expr)
| [] ps      := ([], ps)
| (list.cons b bs) ps :=
  match ps.span (λap:expr × expr, ¬ ap.2 =ₐ b) with
    | (_, [])           := let (bs, ps) := compact_relation bs ps in (b::bs, ps)
    | (ps₁, list.cons (a, _) ps₂) := let i := a.instantiate_local b.local_uniq_name in
      compact_relation (bs.map i) ((ps₁ ++ ps₂).map (λ⟨a, p⟩, (a, i p)))
  end

meta def add_coinductive_predicate'
  (u_names : list name) (params : list expr) (preds : list $ expr × list expr) : command := do
  let params_names := params.map local_pp_name,
  let u_params := u_names.map level.param,

  pre_info ← preds.mmap (λ⟨c, is⟩, do
    (ls, t) ← mk_local_pis c.local_type,
    (is_def_eq t `(Prop) <|>
      fail (format! "Type of {c.local_pp_name} is not Prop. Currently only " ++
                    "coinductive predicates are supported.")),
    let n := if preds.length = 1 then "" else "_" ++ c.local_pp_name.last_string,
    f₁ ← mk_local_def (mk_simple_name $ "C" ++ n) c.local_type,
    f₂ ← mk_local_def (mk_simple_name $ "C₂" ++ n) c.local_type,
    return (ls, (f₁, f₂))),

  let fs := pre_info.map prod.snd,
  let fs₁ := fs.map prod.fst,
  let fs₂ := fs.map prod.snd,

  pds ← (preds.zip pre_info).mmap (λ⟨⟨c, is⟩, ls, f₁, f₂⟩, do
    sort u_f ← infer_type f₁ >>= infer_type,
    let pred_g := λc:expr, (const c.local_uniq_name u_params : expr).app_of_list params,
    intros ← is.mmap (λi, do
      (args, t') ← mk_local_pis i.local_type,
      (name.mk_string sub p) ← return i.local_uniq_name,
      let loc_args := args.map $ λe, (fs₁.zip preds).foldl (λ(e:expr) ⟨f, c, _⟩,
        e.replace_with (pred_g c) f) e,
      let t' := t'.replace_with (pred_g c) f₂,
      return { tactic.add_coinductive_predicate.coind_rule .
        orig_nm  := i.local_uniq_name,
        func_nm  := (p ++ "functional") ++ sub,
        type     := i.local_type,
        loc_type := t'.pis loc_args,
        concl    := t',
        loc_args := loc_args,
        args     := args,
        insts    := t'.get_app_args }),
    return { tactic.add_coinductive_predicate.coind_pred .
      pd_name := c.local_uniq_name, type := c.local_type, f₁ := f₁, f₂ := f₂, u_f := u_f,
      intros := intros, locals := ls, params := params, u_names := u_names }),

  /- Introduce all functionals -/
  pds.mmap' (λpd:coind_pred, do
    let func_f₁ := pd.func_g.app_of_list $ fs₁,
    let func_f₂ := pd.func_g.app_of_list $ fs₂,

    /- Define functional for `pd` as inductive predicate -/
    func_intros ← pd.intros.mmap (λr:coind_rule, do
      let t := instantiate_local pd.f₂.local_uniq_name (pd.func_g.app_of_list fs₁) r.loc_type,
      return (r.func_nm, r.orig_nm, t.pis $ params ++ fs₁)),
    add_inductive pd.func.const_name u_names
      (params.length + preds.length) (pd.type.pis $ params ++ fs₁) (func_intros.map $ λ⟨t, _, r⟩, (t, r)),

    /- Prove monotonicity rule -/
    mono_params ← pds.mmap (λpd, do
      h ← mk_local_def `h $ pd.le pd.f₁ pd.f₂,
      return [pd.f₁, pd.f₂, h]),
    pd.add_theorem (pd.func.const_name ++ "mono")
      ((pd.le func_f₁ func_f₂).pis $ params ++ mono_params.join)
      (do
      ps ← intro_lst $ params.map expr.local_pp_name,
      fs ← pds.mmap (λpd, do
        [f₁, f₂, h] ← intro_lst [pd.f₁.local_pp_name, pd.f₂.local_pp_name, `h],
        -- the type of h' reduces to h
        let h' := local_const h.local_uniq_name h.local_pp_name h.local_binder_info $
          (((const `implies [] : expr)
            (f₁.app_of_list pd.locals) (f₂.app_of_list pd.locals)).pis pd.locals).instantiate_locals $
          (ps.zip params).map $ λ⟨lv, p⟩, (p.local_uniq_name, lv),
        return (f₂, h')),
      m ← pd.rec',
      eapply $ m.app_of_list ps, -- somehow `induction` / `cases` doesn't work?
      func_intros.mmap' (λ⟨n, pp_n, t⟩, solve1 $ do
        bs ← intros,
        ms ← apply_core ((const n u_params).app_of_list $ ps ++ fs.map prod.fst) {new_goals := new_goals.all},
        params ← (ms.zip bs).enum.mfilter (λ⟨n, m, d⟩, bnot <$> is_assigned m.2),
        params.mmap' (λ⟨n, m, d⟩, mono d (fs.map prod.snd) <|>
          fail format! "failed to prove montonoicity of {n+1}. parameter of intro-rule {pp_n}")))),

  pds.mmap' (λpd, do
    let func_f := λpd:coind_pred, pd.func_g.app_of_list $ pds.map coind_pred.f₁,

    /- define final predicate -/
    pred_body ← mk_exists_lst (pds.map coind_pred.f₁) $
      mk_and_lst $ (pds.map $ λpd, pd.le pd.f₁ (func_f pd)) ++ [pd.f₁.app_of_list pd.locals],
    add_decl $ mk_definition pd.pd_name u_names (pd.type.pis $ params) $
      pred_body.lambdas $ params ++ pd.locals,

    /- prove `corec_functional` rule -/
    hs ← pds.mmap $ λpd:coind_pred, mk_local_def `hc $ pd.le pd.f₁ (func_f pd),
    pd.add_theorem (pd.pred.const_name ++ "corec_functional")
      ((pd.le pd.f₁ pd.pred_g).pis $ params ++ fs₁ ++ hs)
      (do
      intro_lst $ params.map local_pp_name,
      fs ← intro_lst $ fs₁.map local_pp_name,
      hs ← intro_lst $ hs.map local_pp_name,
      ls ← intro_lst $ pd.locals.map local_pp_name,
      h ← intro `h,
      whnf_target,
      fs.mmap' existsi,
      hs.mmap' (λf, econstructor >> exact f),
      exact h)),

  let func_f := λpd : coind_pred, pd.func_g.app_of_list $ pds.map coind_pred.pred_g,

  /- prove `destruct` rules -/
  pds.enum.mmap' (λ⟨n, pd⟩, do
    let destruct := pd.le pd.pred_g (func_f pd),
    pd.add_theorem (pd.pred.const_name ++ "destruct") (destruct.pis params) (do
      ps ← intro_lst $ params.map local_pp_name,
      ls ← intro_lst $ pd.locals.map local_pp_name,
      h ← intro `h,
      (fs, h) ← elim_gen_prod pds.length h [],
      (hs, h) ← elim_gen_prod pds.length h [],
      eapply $ pd.mono.app_of_list ps,
      pds.mmap' (λpd:coind_pred, focus1 $ do
        eapply $ pd.corec_functional,
        focus $ hs.map exact),
      some h' ← return $ hs.nth n,
      eapply h',
      exact h)),

  /- prove `construct` rules -/
  pds.mmap' (λpd,
    pd.add_theorem (pd.pred.const_name ++ "construct")
      ((pd.le (func_f pd) pd.pred_g).pis params) (do
      ps ← intro_lst $ params.map local_pp_name,
      let func_pred_g := λpd:coind_pred,
        pd.func.app_of_list $ ps ++ pds.map (λpd:coind_pred, pd.pred.app_of_list ps),
      eapply $ pd.corec_functional.app_of_list $ ps ++ pds.map func_pred_g,
      pds.mmap' (λpd:coind_pred, solve1 $ do
        eapply $ pd.mono.app_of_list ps,
        pds.mmap' (λpd, solve1 $ eapply (pd.destruct.app_of_list ps) >> skip)))),

  /- prove `cases_on` rules -/
  pds.mmap' (λpd, do
    let C := pd.f₁.to_implicit_binder,
    h ← mk_local_def `h $ pd.pred_g.app_of_list pd.locals,
    rules ← pd.intros.mmap (λr:coind_rule, do
      mk_local_def (mk_simple_name r.orig_nm.last_string) $ (C.app_of_list r.insts).pis r.args),
    cases_on ← pd.add_theorem (pd.pred.const_name ++ "cases_on")
      ((C.app_of_list pd.locals).pis $ params ++ [C] ++ pd.impl_locals ++ [h] ++ rules)
      (do
        ps ← intro_lst $ params.map local_pp_name,
        C  ← intro `C,
        ls ← intro_lst $ pd.locals.map local_pp_name,
        h  ← intro `h,
        rules  ← intro_lst $ rules.map local_pp_name,
        func_rec ← pd.rec',
        eapply $ func_rec.app_of_list $ ps ++ pds.map (λpd, pd.pred.app_of_list ps) ++ [C] ++ rules,
        eapply $ pd.destruct,
        exact h),
    set_basic_attribute `elab_as_eliminator cases_on.const_name),

  /- prove `corec_on` rules -/
  pds.mmap' (λpd, do
    rules ← pds.mmap (λpd, do
      intros ← pd.intros.mmap (λr, do
        let (bs, eqs) := compact_relation r.loc_args $ pd.locals.zip r.insts,
        eqs ← eqs.mmap (λ⟨l, i⟩, do
          sort u ← infer_type l.local_type,
          return $ (const `eq [u] : expr) l.local_type i l),
        match bs, eqs with
        | [], [] := return ((0, 0), mk_true)
        | _, []  := prod.mk (bs.length, 0) <$> mk_exists_lst bs.init bs.ilast.local_type
        | _, _   := prod.mk (bs.length, eqs.length) <$> mk_exists_lst bs (mk_and_lst eqs)
        end),
      let shape  := intros.map prod.fst,
      let intros := intros.map prod.snd,
      prod.mk shape <$>
        mk_local_def (mk_simple_name $ "h_" ++ pd.pd_name.last_string)
          (((pd.f₁.app_of_list pd.locals).imp (mk_or_lst intros)).pis pd.locals)),
    let shape := rules.map prod.fst,
    let rules := rules.map prod.snd,
    h ← mk_local_def `h $ pd.f₁.app_of_list pd.locals,
    pd.add_theorem (pd.pred.const_name ++ "corec_on")
      ((pd.pred_g.app_of_list $ pd.locals).pis $ params ++ fs₁ ++ pd.impl_locals ++ [h] ++ rules)
      (do
        ps ← intro_lst $ params.map local_pp_name,
        fs ← intro_lst $ fs₁.map local_pp_name,
        ls ← intro_lst $ pd.locals.map local_pp_name,
        h  ← intro `h,
        rules  ← intro_lst $ rules.map local_pp_name,
        eapply $ pd.corec_functional.app_of_list $ ps ++ fs,
        (pds.zip $ rules.zip shape).mmap (λ⟨pd, hr, s⟩, solve1 $ do
          ls ← intro_lst $ pd.locals.map local_pp_name,
          h' ← intro `h,
          h' ← note `h' none $ hr.app_of_list ls h',
          match s.length with
          | 0     := induction h' >> skip -- h' : false
          | (n+1) := do
            hs ← elim_gen_sum n h',
            (hs.zip $ pd.intros.zip s).mmap' (λ⟨h, r, n_bs, n_eqs⟩, solve1 $ do
              (as, h) ← elim_gen_prod (n_bs - (if n_eqs = 0 then 1 else 0)) h [],
              if n_eqs > 0 then do
                (eqs, eq') ← elim_gen_prod (n_eqs - 1) h [],
                (eqs ++ [eq']).mmap' subst
              else skip,
              eapply ((const r.func_nm u_params).app_of_list $ ps ++ fs),
              iterate assumption)
          end),
        exact h)),

  /- prove constructors -/
  pds.mmap' (λpd, pd.intros.mmap' (λr,
    pd.add_theorem r.orig_nm (r.type.pis params) $ do
      ps ← intro_lst $ params.map local_pp_name,
      bs ← intros,
      eapply $ pd.construct,
      exact $ (const r.func_nm u_params).app_of_list $ ps ++ pds.map (λpd, pd.pred.app_of_list ps) ++ bs)),

  pds.mmap' (λpd:coind_pred, set_basic_attribute `irreducible pd.pd_name),

  try triv -- we setup a trivial goal for the tactic framework

meta def mk_bisim_rel (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
do let my_t := (@const tt d.induct.name d.induct.u_params).mk_app d.params,
   trace_expr my_t,
   let params := (d.params.map to_implicit),
   let bisim_n := d.induct.name <.> "bisim",
   -- t ← pis d.params $ imp my_t $ my_t.imp `(Prop),
   -- let t := imp my_t $ my_t.imp `(Prop),
   -- let sig := local_const bisim_n bisim_n binder_info.default t,
   -- sig ← mk_local_def bisim_n t,
   let bisim_c := (@const tt bisim_n d.induct.u_params),
   -- let bisim_c := sig.mk_app d.params,
   -- let bisim_c := sig,
   cs ← d.induct.ctors.mmap $ λ c,
   do { let (as,bs)  := c.args.enum.partition $ λ e : _ × _, my_t.occurs e.2,
        trace "===",
        as' ← as.mmap $ bitraversable.tsnd renew,
        trace as,
        as.mmap $ trace_expr ∘ prod.snd,
        trace bs,
        bs.mmap $ trace_expr ∘ prod.snd,

        c.args.mmap infer_type >>= trace,
        let args' := list.merge (inv_image (<) prod.fst) as' bs,
        -- let x := (@const tt c.name d.induct.u_params).mk_app d.params,
        let x := (@const tt c.name d.induct.u_params),
        let y := x.mk_app $ args'.map prod.snd,
        let x := x.mk_app c.args,
        -- let t := bisim_c x y,
        let vs := (list.merge (inv_image (<) prod.fst) args' as).map prod.snd,
        hs ← mzip_with (λ a b : ℕ × expr,
          do (vs,t) ← infer_type a.2 >>= mk_local_pis,
             let x := a.2.mk_app vs,
             let y := b.2.mk_app vs,
             pis vs (bisim_c x y) >>= mk_local_def `a) as as',
        -- t ← pis (d.params ++ vs ++ hs) t,
        -- trace t.list_local_consts,
        -- trace t,
        -- trace vs,
        let n := c.name.update_prefix bisim_n,
        trace n,
        pure { type_cnstr . name := n, args := vs ++ hs, result := [x,y], } },
   -- let decl : single_inductive_decl :=
   --     { attrs := attr,
   --       sig := imp my_t $ my_t.imp `(Prop),
   --       intros := _ },
   -- let decl : inductive_decl :=
   --     { u_names := d.induct.u_names,
   --       params := d.params,
   --       decls := [decl] },
   trace d.induct.pre,
   let idx := local_const `α `α binder_info.default my_t,
   let ind :=
       { inductive_type . pre := d.induct.pre,
                          name := bisim_n,
                          u_names := d.induct.u_names,
                          params := params,
                          idx := [idx,idx],
                          type := `(Prop),
                          ctors := cs },
   format_inductive ind >>= trace,
   let d := inductive_type.to_decl ind,
   d' ← d.decls.nth 0,
   -- trace $ d'.sig.to_raw_fmt,
   -- trace $ d'.intros.map to_raw_fmt,
   trace (d.decls.map $ λ c, (to_raw_fmt c.sig, c.sig.list_local_consts, c.intros.map expr.list_local_consts)),
   add_coinductive_predicate' d.u_names d.params (d.decls.map $ λ c, (c.sig, c.intros)),
   -- decl.decls.mmap' $ λ d, do {
   --   updateex_env $ λ env, pure $ env.add_namespace d.name
   --   -- meta_info.attrs.apply d.name,
   --   -- d.attrs.apply d.name
   --   -- some doc_string ← pure meta_info.doc_string | skip,
   --   -- add_doc_string d.name doc_string
   -- },
   pure ()


meta def mk_bisim (func : datatype_shape) (d : internal_mvfunctor) : tactic unit :=
do let my_shape_intl_t := (@const tt (d.induct.name <.> "shape" <.> "internal") d.induct.u_params).mk_app (func.dead_params.map prod.fst),
   let my_shape_t := (@const tt (d.induct.name <.> "shape") d.induct.u_params).mk_app func.params,
   v_t ← mk_local_def `x my_shape_t,
   let X := to_implicit func.hole,
   C ← lambdas [v_t] X,
   v' ← mk_live_vec d.vec_lvl $ X :: d.live_params.map prod.fst,
   let cases_on := d.induct.name <.> "shape" <.> "cases_on",
   let cases_u : list level := level.succ d.vec_lvl :: d.induct.u_params,
   let fs := (@const tt cases_on $ cases_u).mk_app $ func.params ++ [C,v_t],
   df ← mk_mapp ``mvqpf.fix.rec [none,my_shape_intl_t,none,none] >>= trace_expr,
   pure ()

@[user_command]
meta def data_decl (meta_info : decl_meta_info) (_ : parse (tk "data")) : parser unit :=
do d ← inductive_decl.parse meta_info,
   (func,d) ← mk_datatype ``mvqpf.fix d,
   trace_error $ mk_constr ``mvqpf.fix.mk d,
   trace_error $ mk_destr ``mvqpf.fix.dest ``mvqpf.fix.mk ``mvqpf.fix.mk_dest func d,
   trace_error $ mk_recursor func d,
   trace_error $ mk_dep_recursor func d,
   pure ()

@[user_command]
meta def codata_decl (meta_info : decl_meta_info) (_ : parse (tk "codata")) : parser unit :=
do d ← inductive_decl.parse meta_info,
   decl ← d.decls.nth 0,
   -- trace $ decl.intros.map to_fmt,
   trace $ decl.sig.to_raw_fmt,
   trace $ decl.intros.map to_raw_fmt,
   (func,d) ← mk_datatype ``mvqpf.cofix d,
   trace_error $ mk_constr ``mvqpf.cofix.mk d,
   trace_error $ mk_destr ``mvqpf.cofix.dest ``mvqpf.cofix.mk ``mvqpf.cofix.mk_dest func d,
   trace_error $ mk_corecursor func d,
   trace_error $ mk_bisim_rel func d,
   -- trace_error $ mk_bisim func d,
   pure ()

end tactic

universes u

-- namespace foo

codata stream' (γ α β γ' : Type u) : Type u
| zero : γ → stream'
| succ : γ' → α → (ℤ → β → stream') → stream'

-- codata foo.stream' (γ α β γ' : Type u) : Type u
-- | zero : γ → foo.stream'
-- | succ : γ' → α → (ℤ → β → foo.stream') → foo.stream'

-- end foo
#print stream'.internal
#print stream'.shape.internal

data nat'
| zero : nat'
| succ : nat' → nat'

#print nat'
#print nat'.internal
#print nat'.shape
#print nat'.shape.internal

#check nat'.rec
#check @nat'.drec
#print nat'.zero
#print nat'.succ

-- #exit

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

#check @mvqpf.cofix.bisim
-- mvqpf.cofix.bisim :
--   ∀ {n : ℕ} {F : typevec (n + 1) → Type u_1} [_inst_1 : mvfunctor F] [q : mvqpf F] {α : typevec n}
--   (r : mvqpf.cofix F α → mvqpf.cofix F α → Prop),
--     (∀ (x y : mvqpf.cofix F α),
--        r x y →
--        (typevec.id ::: quot.mk r) <$$> mvqpf.cofix.dest x = (typevec.id ::: quot.mk r) <$$> mvqpf.cofix.dest y) →
--     ∀ (x y : mvqpf.cofix F α), r x y → x = y

section bisim

variables {α : Type u}
coinductive bisim : stream α → stream α → Prop
| nil : bisim (stream.zero α) (stream.zero α)
| cons (a : α) (x y : stream α) : bisim x y → bisim (stream.succ _ a x) (stream.succ _ a y)

-- variables h₀ : r (stream.zero α) (stream.zero α)
-- variables h₁ : ∀ (a : α) (x y : stream α), r (stream.succ _ a x) (stream.succ _ a y) → r x y
#print prefix hidden.bisim
def eq_of_bisim : Π (s₀ s₁ : stream α) (h' : bisim s₀ s₁), s₀ = s₁ :=
mvqpf.cofix.bisim bisim
begin
  intros,
  apply hidden.bisim.cases_on a; clear a, refl,
  intros,
end
-- (λ x y ih, by { induction x using hidden.stream.cases_on,
--                 induction y using hidden.stream.cases_on,
--                 { dunfold stream.zero, erw [mvqpf.cofix.dest_mk], }, } )
#exit
end bisim

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

data list' (γ α β γ' : Type u) : Type u
| zero : γ → list'
| succ : γ' → α → (ℤ → β → list') → list'

#print list'.rec
#check list'.drec
#print list'.shape.internal.map

-- codata stream₁ (α : Type u) : Type u
-- | zero : stream₁
-- | succ : α → (list stream₁) → stream₁

-- #print hidden.stream₁.internal
-- #print hidden.stream₁
-- #print hidden.stream₁.shape
-- #print hidden.stream₁.corec

end hidden
