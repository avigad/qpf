/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Multivariate quotients of polynomial functors.
-/
import ..mvpfunctor.W
universe u

class mvqpf {n : ℕ} (F : typevec.{u} n → Type*) [mvfunctor F] :=
(P         : mvpfunctor.{u} n)
(abs       : Π {α}, P.apply α → F α)
(repr      : Π {α}, F α → P.apply α)
(abs_repr  : ∀ {α} (x : F α), abs (repr x) = x)
(abs_map   : ∀ {α β} (f : α ⟹ β) (p : P.apply α), abs (f <$$> p) = f <$$> abs p)

namespace mvqpf
variables {n : ℕ} {F : typevec.{u} n → Type*} [mvfunctor F] [q : mvqpf F]
include q
open mvfunctor (liftp liftr)

-- def repr {α : typevec n} (x : F α) := repr' x

-- theorem abs_repr {α : typevec n} (x : F α) : abs (repr x) = x :=
-- abs_repr' x

/-
Show that every mvqpf is a lawful mvfunctor.
-/

protected theorem id_map {α : typevec n} (x : F α) : typevec.id <$$> x = x :=
by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map], reflexivity }

theorem comp_map {α β γ : typevec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α) :
  (g ⊚ f) <$$> x = g <$$> f <$$> x :=
by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map, ←abs_map, ←abs_map], reflexivity }

instance is_lawful_mvfunctor : mvfunctor.is_lawful F :=
{ id_map := @mvqpf.id_map n F _ _,
  comp_map := @comp_map n F _ _ }

/- Lifting predicates and relations -/

theorem liftp_iff {α : typevec n} (p : Π ⦃i⦄, α i → Prop) (x : F α) :
  liftp p x ↔ ∃ a f, x = abs ⟨a, f⟩ ∧ ∀ i j, p (f i j) :=
begin
  split,
  { rintros ⟨y, hy⟩, cases h : repr y with a f,
    use [a, λ i j, (f i j).val], split,
    { rw [←hy, ←abs_repr y, h, ←abs_map], reflexivity },
    intros i j, apply (f i j).property },
  rintros ⟨a, f, h₀, h₁⟩, dsimp at *,
  use abs (⟨a, λ i j, ⟨f i j, h₁ i j⟩⟩),
  rw [←abs_map, h₀], reflexivity
end

theorem liftr_iff {α : typevec n} (r : Π ⦃i⦄, α i → α i → Prop) (x y : F α) :
  liftr r x y ↔ ∃ a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) :=
begin
  split,
  { rintros ⟨u, xeq, yeq⟩, cases h : repr u with a f,
    use [a, λ i j, (f i j).val.fst, λ i j, (f i j).val.snd],
    split, { rw [←xeq, ←abs_repr u, h, ←abs_map], refl },
    split, { rw [←yeq, ←abs_repr u, h, ←abs_map], refl },
    intros i j, exact (f i j).property },
  rintros ⟨a, f₀, f₁, xeq, yeq, h⟩,
  use abs ⟨a, λ i j, ⟨(f₀ i j, f₁ i j), h i j⟩⟩,
  dsimp, split,
  { rw [xeq, ←abs_map], refl },
  rw [yeq, ←abs_map], refl
end

end mvqpf
