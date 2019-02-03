/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Multivariate polynomial functors.

Note: eventually the W and M constructions as multivariate polynomial functors will go here.
-/
import ..mvfunctor
import for_mathlib
universes u v

/-
multivariate polynomial functors
-/

structure mvpfunctor (n : ℕ) :=
(A : Type.{u}) (B : A → typevec.{u} n)

namespace mvpfunctor
open mvfunctor (liftp liftr)

variables {n m : ℕ} (P : mvpfunctor.{u} n)

def apply (α : typevec.{u} n) : Type u := Σ a : P.A, P.B a ⟹ α

def map {α β : typevec n} (f : α ⟹ β) : P.apply α → P.apply β :=
λ ⟨a, g⟩, ⟨a, typevec.comp f g⟩

instance : mvfunctor P.apply :=
⟨@mvpfunctor.map n P⟩

theorem map_eq {α β : typevec n} (g : α ⟹ β) (a : P.A) (f : P.B a ⟹ α) :
  @mvfunctor.map _ P.apply _ _ _ g ⟨a, f⟩ = ⟨a, g ⊚ f⟩ :=
rfl

theorem id_map {α : typevec n} : ∀ x : P.apply α, typevec.id <$$> x = x
| ⟨a, g⟩ := rfl

theorem comp_map {α β γ : typevec n} (f : α ⟹ β) (g : β ⟹ γ) :
  ∀ x : P.apply α, (g ⊚ f) <$$> x = g <$$> (f <$$> x)
| ⟨a, h⟩ := rfl

def comp (P : mvpfunctor.{u} n) (Q : fin' n → mvpfunctor.{u} m) : mvpfunctor m :=
{ A := Σ a₂ : P.1, Π i, P.2 a₂ i → (Q i).1,
  B := λ a, λ i, Σ j (b : P.2 a.1 j), (Q j).2 (a.snd j b) i }

variables {P} {Q : fin' n → mvpfunctor.{u} m} {α β : typevec.{u} m}

def comp.mk (x : P.apply (λ i, (Q i).apply α)) : (comp P Q).apply α :=
⟨ ⟨ x.1, λ i a, (x.2 _ a).1  ⟩, λ i a, (x.snd a.fst (a.snd).fst).snd i (a.snd).snd ⟩

def comp.get (x : (comp P Q).apply α) : P.apply (λ i, (Q i).apply α) :=
⟨ x.1.1, λ i a, ⟨x.fst.snd i a, λ (j : fin' m) (b : (Q i).B _ j), x.snd j ⟨i, ⟨a, b⟩⟩⟩ ⟩

lemma comp.get_map (f : α ⟹ β) (x : (comp P Q).apply α) :
  comp.get (f <$$> x) = (λ i (x : (Q i).apply α), f <$$> x) <$$> comp.get x :=
by cases x; refl

@[simp]
lemma comp.get_mk (x : P.apply (λ i, (Q i).apply α)) : comp.get (comp.mk x) = x :=
begin
  cases x,
  simp! [comp.get,comp.mk],
  ext; intros; refl
end

@[simp]
lemma comp.mk_get (x : (comp P Q).apply α) : comp.mk (comp.get x) = x :=
begin
  cases x,
  dsimp [comp.get,comp.mk],
  ext; intros, refl, refl,
  congr, ext; intros; refl,
  ext, congr, rcases x_1 with ⟨a,b,c⟩; refl,
end

theorem liftp_iff {α : typevec n} (p : Π ⦃i⦄ , α i → Prop) (x : P.apply α) :
  liftp p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i j, p (f i j) :=
begin
  split,
  { rintros ⟨y, hy⟩, cases h : y with a f,
    refine ⟨a, λ i j, (f i j).val, _, λ i j, (f i j).property⟩,
    rw [←hy, h, map_eq], refl },
  rintros ⟨a, f, xeq, pf⟩,
  use ⟨a, λ i j, ⟨f i j, pf i j⟩⟩,
  rw [xeq], reflexivity
end

theorem liftr_iff {α : typevec n} (r : Π ⦃i⦄, α i → α i → Prop) (x y : P.apply α) :
  liftr r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) :=
begin
  split,
  { rintros ⟨u, xeq, yeq⟩, cases h : u with a f,
    use [a, λ i j, (f i j).val.fst, λ i j, (f i j).val.snd],
    split, { rw [←xeq, h], refl },
    split, { rw [←yeq, h], refl },
    intros i j, exact (f i j).property },
  rintros ⟨a, f₀, f₁, xeq, yeq, h⟩,
  use ⟨a, λ i j, ⟨(f₀ i j, f₁ i j), h i j⟩⟩,
  dsimp, split,
  { rw [xeq], refl },
  rw [yeq], refl
end

end mvpfunctor
