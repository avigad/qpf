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
    rintros a₁ a₂ ⟨r, pr, ra₁a₂⟩, apply quot.sound,
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
    show r' (g <$$> a₁) (g <$$> a₂), from ⟨a₁, a₂, ra₁a₂, rfl, rfl⟩
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

theorem cofix.dest_corec {α : typevec n} {β : Type u} (g : β → F (α.append1 β)) (x : β) :
  cofix.dest (cofix.corec g x) = append_fun id (cofix.corec g) <$$> g x :=
begin
  conv { to_lhs, rw [cofix.dest, cofix.corec] }, dsimp,
  rw [corecF_eq, abs_map, abs_repr, ←comp_map, ←append_fun_comp], reflexivity
end

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
  rw [cofix.mk, cofix.dest_corec, ←comp_map, ←cofix.mk, ← append_fun_comp, this, id_comp, append_fun_id_id, id_map]
end

noncomputable instance mvqpf_cofix (α : typevec n) : mvqpf (cofix F) :=
{ P         := q.P.Mp,
  abs       := λ α, quot.mk Mcongr,
  repr'     := λ α, quot.out,
  abs_repr' := λ α, quot.out_eq,
  abs_map   := λ α β g x, rfl
}

end mvqpf
