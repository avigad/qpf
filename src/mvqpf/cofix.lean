/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The initial algebra of a multivariate qpf is again a qpf.
-/
import ..mvpfunctor.M .basic
universe u

namespace mvqpf
open typevec
open mvfunctor (liftp liftr)

variables {n : ℕ} {F : typevec.{u} (n+1) → Type u} [mvfunctor F] [q : mvqpf F]
include q

def corecF {α : typevec n} {β : Type*} (g : β → F (α.append1 β)) : β → q.P.M α :=
q.P.M_corec (λ x, repr (g x))

theorem corecF_eq {α : typevec n} {β : Type*} (g : β → F (α.append1 β)) (x : β) :
  q.P.M_dest (corecF g x) = append_fun id (corecF g) <$$> repr (g x) :=
by rw [corecF, q.P.M_dest_corec]

def is_precongr {α : typevec n} (r : q.P.M α → q.P.M α → Prop) : Prop :=
  ∀ ⦃x y⦄, r x y →
    abs (append_fun id (quot.mk r) <$$> q.P.M_dest x) =
      abs (append_fun id (quot.mk r) <$$> q.P.M_dest y)

def Mcongr {α : typevec n} : q.P.M α → q.P.M α → Prop :=
λ x y, ∃ r, is_precongr r ∧ r x y

def cofix (F : typevec (n + 1) → Type u) [mvfunctor F] [q : mvqpf F] (α : typevec n):=
quot (@Mcongr _ F _ q α)

def cofix.map {α β : typevec n} (g : α ⟹ β) : cofix F α → cofix F β :=
quot.lift (λ x : q.P.M α, quot.mk Mcongr (g <$$> x))
  begin
    rintros aa₁ aa₂ ⟨r, pr, ra₁a₂⟩, apply quot.sound,
    let r' := λ b₁ b₂, ∃ a₁ a₂ : q.P.M α, r a₁ a₂ ∧ b₁ = g <$$> a₁ ∧ b₂ = g <$$> a₂,
    use r', split,
    { show is_precongr r',
      rintros b₁ b₂ ⟨a₁, a₂, ra₁a₂, b₁eq, b₂eq⟩,
      let u : quot r → quot r' := quot.lift (λ x : q.P.M α, quot.mk r' (g <$$> x))
        (by { intros a₁ a₂ ra₁a₂, apply quot.sound, exact ⟨a₁, a₂, ra₁a₂, rfl, rfl⟩ }),
      have hu : (quot.mk r' ∘ λ x : q.P.M α, g <$$> x) = u ∘ quot.mk r,
        { ext x, refl },
      rw [b₁eq, b₂eq, q.P.M_dest_map, q.P.M_dest_map, ←q.P.comp_map, ←q.P.comp_map],
      rw [←append_fun_comp, id_comp, hu, hu, ←comp_id g, append_fun_comp],
      rw [q.P.comp_map, q.P.comp_map, abs_map, pr ra₁a₂, ←abs_map] },
    show r' (g <$$> aa₁) (g <$$> aa₂), from ⟨aa₁, aa₂, ra₁a₂, rfl, rfl⟩
  end

instance cofix.mvfunctor : mvfunctor (cofix F) :=
{ map := @cofix.map _ _ _ _}

def cofix.corec {α : typevec n} {β : Type u} (g : β → F (α.append1 β)) : β → cofix F α :=
λ x, quot.mk  _ (corecF g x)

def cofix.dest {α : typevec n} : cofix F α → F (α.append1 (cofix F α)) :=
quot.lift
  (λ x, append_fun id (quot.mk Mcongr) <$$> (abs (q.P.M_dest x)))
  begin
    rintros x y ⟨r, pr, rxy⟩, dsimp,
    have : ∀ x y, r x y → Mcongr x y,
    { intros x y h, exact ⟨r, pr, h⟩ },
    rw [←quot.factor_mk_eq _ _ this], dsimp,
    conv { to_lhs,
      rw [append_fun_comp_id, comp_map, ←abs_map, pr rxy, abs_map, ←comp_map,
        ←append_fun_comp_id] }
  end
-- #check exit

def cofix.corec'₁ {α : typevec n} {β : Type u}
  (g : Π {X}, (β → X) → F (α.append1 X)) (x : β) : cofix F α :=
cofix.corec (λ x, g id) x

-- def cofix.corec' {α : typevec n} {β : Type u} (g : β → F (α.append1 (cofix F α ⊕ β))) (x : β) : cofix F α :=
-- cofix.corec
-- (λ x : cofix F α ⊕ β,
-- match x with
-- | (sum.inl val) := (id ::: sum.inl) <$$> cofix.dest val
-- | (sum.inr val) := g val
-- end)
-- (sum.inr x)

def cofix.corec' {α : typevec n} {β : Type u} (g : β → F (α.append1 (cofix F α ⊕ β))) (x : β) : cofix F α :=
let f : α ::: cofix F α ⟹ α ::: (cofix F α ⊕ β) := id ::: sum.inl in
cofix.corec
(sum.elim (mvfunctor.map f ∘ cofix.dest) g)
(sum.inr x : cofix F α ⊕ β)

def cofix.corec₁ {α : typevec n} {β : Type u}
  (g : Π {X}, (cofix F α → X) → (β → X) → β → F (α.append1 X)) (x : β) : cofix F α :=
cofix.corec' (λ x, g sum.inl sum.inr x) x

-- def cofix.corec₂ {α : typevec n} {β : Type u} {γ : β → Type u}
--   (g : Π {X}, (cofix F α → X) → (Π b, γ b → X) → F (α.append1 X)) (x : β) (y : γ x) :
--   cofix F α :=
-- cofix.corec₁ (λ X ex rec, g ex $ λ a b, rec $ sigma.mk a b) (sigma.mk x y)

-- def cofix.corec₃ {α : typevec n} {β : Type u} {γ : β → Type u} {φ : Π a, γ a → Type u}
--   (g : Π {X}, (cofix F α → X) → (Π b (c : γ b), φ b c → X) → F (α.append1 X)) (x : β) (y : γ x) (z : φ x y) :
--   cofix F α :=
-- cofix.corec₁
--   (λ X ex rec, g ex $ λ a b c, rec (⟨a, b, c⟩ : Σ a b, φ a b))
--   (sigma.mk x $ sigma.mk y z)

theorem cofix.dest_corec {α : typevec n} {β : Type u} (g : β → F (α.append1 β)) (x : β) :
  cofix.dest (cofix.corec g x) = append_fun id (cofix.corec g) <$$> g x :=
begin
  conv { to_lhs, rw [cofix.dest, cofix.corec] }, dsimp,
  rw [corecF_eq, abs_map, abs_repr, ←comp_map, ←append_fun_comp], reflexivity
end

-- theorem cofix.dest_corec' {α : typevec n} {β : Type u}
--   (g : Π {X}, (β → X) → F (α.append1 X)) (x : β)
--   (h : ∀ X (f : β → X), g f = (id ::: f) <$$> g id ) :
--   cofix.dest (cofix.corec'₁ @g x) = g (cofix.corec'₁ @g) :=
-- begin
--   rw [cofix.corec'₁,cofix.dest_corec,← h], refl
-- end

-- #exit
def cofix.mk {α : typevec n} : F (α.append1 $ cofix F α) → cofix F α :=
cofix.corec (λ x, append_fun id (λ i : cofix F α, cofix.dest.{u} i) <$$> x)

private theorem cofix.bisim_aux {α : typevec n}
    (r : cofix F α → cofix F α → Prop)
    (h' : ∀ x, r x x)
    (h : ∀ x y, r x y →
      append_fun id (quot.mk r) <$$> cofix.dest x = append_fun id (quot.mk r) <$$> cofix.dest y) :
  ∀ x y, r x y → x = y :=
begin
  intro x, apply quot.induction_on x, clear x,
  intros x y, apply quot.induction_on y, clear y,
  intros y rxy,
  apply quot.sound,
  let r' := λ x y, r (quot.mk _ x) (quot.mk _ y),
  have : is_precongr r',
  { intros a b r'ab,
      have  h₀ :
          append_fun id (quot.mk r ∘ quot.mk Mcongr) <$$> abs (q.P.M_dest a) =
          append_fun id (quot.mk r ∘ quot.mk Mcongr) <$$> abs (q.P.M_dest b) :=
        by rw [append_fun_comp_id, comp_map, comp_map]; exact h _ _ r'ab,
    have h₁ : ∀ u v : q.P.M α, Mcongr u v → quot.mk r' u = quot.mk r' v,
    { intros u v cuv, apply quot.sound, dsimp [r'], rw quot.sound cuv, apply h' },
    let f : quot r → quot r' := quot.lift (quot.lift (quot.mk r') h₁)
      begin
        intro c, apply quot.induction_on c, clear c,
        intros c d, apply quot.induction_on d, clear d,
        intros d rcd, apply quot.sound, apply rcd
      end,
    have : f ∘ quot.mk r ∘ quot.mk Mcongr = quot.mk r' := rfl,
    rw [←this, append_fun_comp_id, q.P.comp_map, q.P.comp_map, abs_map, abs_map, abs_map,
         abs_map, h₀] },
  refine ⟨r', this, rxy⟩
end

theorem cofix.bisim_rel {α : typevec n}
    (r : cofix F α → cofix F α → Prop)
    (h : ∀ x y, r x y →
      append_fun id (quot.mk r) <$$> cofix.dest x = append_fun id (quot.mk r) <$$> cofix.dest y) :
  ∀ x y, r x y → x = y :=
let r' x y := x = y ∨ r x y in
begin
  intros x y rxy,
  apply cofix.bisim_aux r',
  { intro x, left, reflexivity },
  { intros x y r'xy,
    cases r'xy, { rw r'xy },
    have : ∀ x y, r x y → r' x y := λ x y h, or.inr h,
    rw ←quot.factor_mk_eq _ _ this, dsimp,
    rw [append_fun_comp_id, append_fun_comp_id],
    rw [@comp_map _ _ _ q _ _ _ (append_fun id (quot.mk r)),
        @comp_map _ _ _ q _ _ _ (append_fun id (quot.mk r))],
    rw h _ _ r'xy },
  right, exact rxy
end

theorem cofix.bisim {α : typevec n}
    (r : cofix F α → cofix F α → Prop)
    (h : ∀ x y, r x y → liftr (rel_last α r) (cofix.dest x) (cofix.dest y)) :
  ∀ x y, r x y → x = y :=
begin
  apply cofix.bisim_rel,
  intros x y rxy,
  rcases (liftr_iff (rel_last α r) _ _).mp (h x y rxy) with ⟨a, f₀, f₁, dxeq, dyeq, h'⟩,
  rw [dxeq, dyeq, ←abs_map, ←abs_map, mvpfunctor.map_eq, mvpfunctor.map_eq],
  rw [←split_drop_fun_last_fun f₀, ←split_drop_fun_last_fun f₁],
  rw [append_fun_comp_split_fun, append_fun_comp_split_fun],
  rw [id_comp, id_comp],
  congr' 2, ext i j, cases i with _ i; dsimp,
  { change f₀ _ j = f₁ _ j, apply h' _ j },
  apply quot.sound,
  apply h' _ j
end

theorem cofix.bisim₂ {α : typevec n}
    (r : cofix F α → cofix F α → Prop)
    (h : ∀ x y, r x y → liftr' (rel_last' α r) (cofix.dest x) (cofix.dest y)) :
  ∀ x y, r x y → x = y :=
cofix.bisim _ $ by intros; rw ← liftr_last_rel_iff; apply h; assumption

theorem cofix.bisim' {α : typevec n} {β : Type*} (Q : β → Prop) (u v : β → cofix F α)
    (h : ∀ x, Q x → ∃ a f' f₀ f₁,
      cofix.dest (u x) = abs ⟨a, q.P.append_contents f' f₀⟩ ∧
      cofix.dest (v x) = abs ⟨a, q.P.append_contents f' f₁⟩ ∧
      ∀ i, ∃ x', Q x' ∧ f₀ i = u x' ∧ f₁ i = v x') :
  ∀ x, Q x → u x = v x :=
λ x Qx,
let R := λ w z : cofix F α, ∃ x', Q x' ∧ w = u x' ∧ z = v x' in
cofix.bisim R
  (λ x y ⟨x', Qx', xeq, yeq⟩,
    begin
      rcases h x' Qx' with ⟨a, f', f₀, f₁, ux'eq, vx'eq, h'⟩,
      rw liftr_iff,
      refine ⟨a, q.P.append_contents f' f₀, q.P.append_contents f' f₁,
        xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, _⟩,
      intro i, cases i,
      { intro j, apply eq.refl },
      apply h',
    end)
  _ _ ⟨x, Qx, rfl, rfl⟩

lemma cofix.mk_dest {α : typevec n} (x : cofix F α) : cofix.mk (cofix.dest x) = x :=
begin
  apply cofix.bisim_rel (λ x y : cofix F α, x = cofix.mk (cofix.dest y)) _ _ _ rfl, dsimp,
  intros x y h, rw h,
  conv { to_lhs, congr, skip, rw [cofix.mk], rw cofix.dest_corec},
  rw [←comp_map, ←append_fun_comp, id_comp],
  rw [←comp_map, ←append_fun_comp, id_comp, ←cofix.mk],
  congr' 2,
  ext u, apply quot.sound, refl
end

lemma cofix.dest_mk {α : typevec n} (x : F (α.append1 $ cofix F α)) : cofix.dest (cofix.mk x) = x :=
begin
  have : cofix.mk ∘ cofix.dest = @_root_.id (cofix F α) := funext cofix.mk_dest,
  rw [cofix.mk, cofix.dest_corec, ←comp_map, ←cofix.mk, ← append_fun_comp, this, id_comp, append_fun_id_id, mvfunctor.id_map]
end

lemma cofix.ext {α : typevec n} (x y : cofix F α) (h : x.dest = y.dest) : x = y :=
by rw [← cofix.mk_dest x,h,cofix.mk_dest]

lemma cofix.ext_mk {α : typevec n} (x y : F (α ::: cofix F α)) (h : cofix.mk x = cofix.mk  y) : x = y :=
by rw [← cofix.dest_mk x,h,cofix.dest_mk]

-- set_option pp.all true

-- theorem cofix.dest_corec'' {α : typevec n} {β : Type u}
--   (g : β → F (α.append1 (cofix F α ⊕ β))) (x : β) :
--   cofix.dest (cofix.corec' g x) = append_fun id (sum.elim id (cofix.corec' g)) <$$> g x :=
-- begin
--   delta cofix.corec', rw [cofix.dest_corec], dsimp,
--   delta id_rhs, congr, dsimp, rw [sum.elim_inr],
-- end

section
omit q
theorem liftr_map {α β : typevec n} {F' : typevec n → Type u} [mvfunctor F']
  [mvfunctor.is_lawful F']
  (R : β ⊗ β ⟹ repeat n Prop) (x : F' α) (f g : α ⟹ β)
  (h : α ⟹ subtype_ R)
  (hh : subtype_val _ ⊚ h = (f ⊗ g) ⊚ prod.diag) :
  liftr' R (f <$$> x) (g <$$> x) :=
begin
  rw liftr_def,
  existsi h <$$> x,
  rw [mvfunctor.map_map,comp_assoc,hh,← comp_assoc,fst_prod_mk,comp_assoc,fst_diag],
  rw [mvfunctor.map_map,comp_assoc,hh,← comp_assoc,snd_prod_mk,comp_assoc,snd_diag],
  dsimp [liftr'], split; refl,
end

open function
theorem liftr_map_last [mvfunctor.is_lawful F] {α : typevec n} {ι ι'}
  (R : ι' → ι' → Prop) (x : F (α ::: ι)) (f g : ι → ι')
  (hh : ∀ x : ι, R (f x) (g x)) :
  liftr' (rel_last' _ R) ((id ::: f) <$$> x) ((id ::: g) <$$> x) :=
let h : ι → { x : ι' × ι' // uncurry R x } := λ x, ⟨ (f x,g x), hh x ⟩ in
have hh' : subtype_val (repeat_eq α) ⊚ diag_sub = id ⊚ prod.diag,
  by { clear_except, ext i, induction i; [apply i_ih, refl], },
have hh : subtype_val (rel_last' α R) ⊚ (diag_sub ::: h) = (id ::: f ⊗ id ::: g) ⊚ prod.diag,
  by { ext (i|i), { replace hh' := congr_fun (congr_fun hh' x_1_a) x_1, convert hh' using 1,
                    rw [← append_prod_append_fun,prod_id], refl },
       simp [(⊚),append_fun,split_fun,subtype_val,prod.diag,prod.arrow_mk,drop_fun,rel_last',subtype_val], },
liftr_map _ x _ _ (diag_sub ::: h) hh

theorem liftr_map_last' [mvfunctor.is_lawful F] {α : typevec n} {ι}
  (R : ι → ι → Prop) (x : F (α ::: ι)) (f : ι → ι)
  (hh : ∀ x : ι, R (f x) x) :
  liftr' (rel_last' _ R) ((id ::: f) <$$> x) x :=
begin
  have := liftr_map_last R x f id hh,
  rwa [append_fun_id_id,mvfunctor.id_map] at this,
end

end

section tactic

setup_tactic_parser
open tactic
omit q

meta def bisim₂ (e : parse texpr) (ids : parse with_ident_list) : tactic unit :=
do e ← to_expr e,
   (expr.pi n bi d b) ← retrieve $ do {
     generalize e,
     target },
   `(@eq %%t %%l %%r) ← pure b,
   x ← mk_local_def `n d,
   v₀ ← mk_local_def `a t,
   v₁ ← mk_local_def `b t,
   x₀ ← mk_app ``eq [v₀,l.instantiate_var x],
   x₁ ← mk_app ``eq [v₁,r.instantiate_var x],
   xx ← mk_app ``and [x₀,x₁],
   ex ← lambdas [x] xx,
   ex ← mk_app ``Exists [ex] >>= lambdas [v₀,v₁],
   R ← pose `R none ex,
   refine ``(cofix.bisim₂ %%R _ _ _ ⟨_,rfl,rfl⟩),
   let f (a b : name) : name := if a = `_ then b else a,
   let ids := (ids ++ list.repeat `_ 5).zip_with f [`a,`b,`x,`Ha,`Hb],
   (ids₀,w::ids₁) ← pure $ list.split_at 2 ids,
   intro_lst ids₀,
   h ← intro1,
   [(_,[w,h],_)] ← cases_core h [w],
   cases h ids₁,
   pure ()

run_cmd add_interactive [``bisim₂]

end tactic

theorem corec_roll {α : typevec n} {X Y} {x₀ : X}
  (f : X → Y) (g : Y → F (α ::: X)) :
  cofix.corec (g ∘ f) x₀ = cofix.corec (mvfunctor.map (id ::: f) ∘ g) (f x₀) :=
begin
  bisim₂ x₀,
  rw [Ha,Hb,cofix.dest_corec,cofix.dest_corec],
  rw [mvfunctor.map_map,← append_fun_comp_id],
  refine liftr_map_last _ _ _ _ _,
  intros a, refine ⟨a,rfl,rfl⟩
end

theorem cofix.dest_corec' {α : typevec n} {β : Type u}
  (g : β → F (α.append1 (cofix F α ⊕ β))) (x : β) :
  cofix.dest (cofix.corec' g x) = append_fun id (sum.elim id (cofix.corec' g)) <$$> g x :=
begin
  rw [cofix.corec',cofix.dest_corec], dsimp,
  congr, ext (i|i); rw corec_roll; dsimp [cofix.corec'],
  { bisim₂ i,
    rw [Ha,Hb,cofix.dest_corec], dsimp [(∘)],
    repeat { rw [mvfunctor.map_map,← append_fun_comp_id] },
    apply liftr_map_last', dsimp [(∘),R], intros, exact ⟨_,rfl,rfl⟩ },
  { congr, ext, erw [append_fun_id_id], simp [mvfunctor.id_map] },
end

theorem cofix.dest_corec₁ {α : typevec n} {β : Type u}
  (g : Π {X}, (cofix F α → X) → (β → X) → β → F (α.append1 X)) (x : β)
  (h : ∀ X Y (f : cofix F α → X) (f' : β → X) (k : X → Y),
         g (k ∘ f) (k ∘ f') x = (id ::: k) <$$> g f f' x) :
  cofix.dest (cofix.corec₁ @g x) = g id (cofix.corec₁ @g) x :=
by rw [cofix.corec₁,cofix.dest_corec',← h]; refl

-- theorem cofix.dest_corec₂ {α : typevec n} {β : Type u} {γ : β → Type u}
--   (g : Π {X}, (cofix F α → X) → (Π b, γ b → X) → F (α.append1 X))
--   (x : β) (y : γ x)
--   (h : ∀ X (k : cofix F α → X) (f : Π b, γ b → X),
--          g k f =
--             (id ::: sum.elim k (@sigma.rec β γ (λ _, X) f)) <$$> g sum.inl (λ (a : β) (b : γ a), sum.inr (sigma.mk a b)) ) :
--   cofix.dest (cofix.corec₂ @g x y) = g id (cofix.corec₂ @g) :=
-- begin
--   rw [cofix.corec₂,cofix.dest_corec₁], refl,
--   intros, rw h, congr, ext ⟨a,b⟩, refl,
-- end

-- theorem cofix.dest_corec₃ {α : typevec n} {β : Type u} {γ : β → Type u}
--   {φ : Π a, γ a → Type u}
--   (g : Π {X}, (cofix F α → X) → (Π b (c : γ b), φ b c → X) → F (α.append1 X))
--   (x : β) (y : γ x) (z : φ x y)
--   (h : ∀ X (k : cofix F α → X) (f : Π b (c : γ b), φ b c → X),
--          g k f =
--             (id ::: sum.elim k (@sigma.rec β (λ x : β, sigma (φ x)) (λ x,X) (λ x, @sigma.rec (γ x) (φ x) (λ _, X) (f x)))) <$$>
--            g sum.inl (λ (a : β) (b : γ a) (c : φ a b), sum.inr (sigma.mk a $ @sigma.mk _ (φ a) b c)) ) :
--   cofix.dest (cofix.corec₃ @g x y z) = g id (cofix.corec₃ @g) :=
-- begin
--   rw [cofix.corec₃,cofix.dest_corec₁], refl,
--   intros, rw h, congr, ext ⟨a,b,c⟩, refl,
-- end

-- #exit
-- theorem cofix.dest_corec'' {α : typevec n} {β : Type u}
--   (g : β → F (α.append1 β)) (x : β) :
--   cofix.dest (cofix.corec g x) = append_fun id (cofix.corec g) <$$> g x :=

-- theorem cofix.dest_corec'' {α : typevec n} {β : Type u}
--   (g : β → F (α.append1 (cofix F α ⊕ β))) (x : β) :
--   cofix.dest (cofix.corec₁ g x) = append_fun id (sum.elim id (cofix.corec' g)) <$$> g x :=
-- begin
--   delta cofix.corec', rw [cofix.dest_corec], dsimp,
--   delta id_rhs,

-- done,
-- congr' 1,
--   ext (a|a),
--   { dsimp [sum.elim], delta id_rhs,
--     -- let f : F (α ::: _) ⊕ β → _ :=
--     -- (sum.elim (λ (val : cofix F α), (id ::: sum.inl) <$$> cofix.dest val) (λ (val : β), g val)),
--     generalize hf : sum.rec _ _ = f,
--     let R : cofix F α → cofix F α → Prop := λ x y, x = cofix.corec f (sum.inl y),
--     refine cofix.bisim R _ _ _ rfl,
--     introv h,
--     dsimp [R] at h,
--     rw [h,← liftr_last_rel_iff,liftr_def],
--     let x' := append_fun id _ <$$> cofix.dest x_1,
--     -- done,
--     apply cofix.ext,
--     rw [cofix.dest_corec], dsimp,
--     rw [mvfunctor.map_map,← append_fun_comp_id], }
-- end

noncomputable instance mvqpf_cofix : mvqpf (cofix F) :=
{ P         := q.P.Mp,
  abs       := λ α, quot.mk Mcongr,
  repr      := λ α, quot.out,
  abs_repr  := λ α, quot.out_eq,
  abs_map   := λ α β g x, rfl
}

end mvqpf
