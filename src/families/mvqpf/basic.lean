/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Multivariate quotients of polynomial functors.
-/
import ..mvpfunctor.W
universe u

class mvqpf {I J : Type u} (F : fam I ⥤ fam J) :=
(P         : mvpfunctor.{u} I J)
(abs       : Π α, P.obj α ⟶ F.obj α)
(repr      : Π α, F.obj α ⟶ P.obj α)
(abs_repr  : ∀ α, repr α ≫ abs α = 𝟙 _)
(abs_map   : ∀ {α β} (f : α ⟶ β), P.map f ≫ abs _ = abs _ ≫ F.map f)

namespace mvqpf
variables {I J : Type u} {F : fam I ⥤ fam J} [q : mvqpf F]
open pfunctor (liftp liftr)

-- def repr {α : typevec n} (x : F α) := repr' n x

-- theorem abs_repr {α : fam I} (x : F α) : abs (repr x) = x :=
-- abs_repr' n x

/-
Show that every mvqpf is a lawful mvfunctor.
-/
include q

theorem abs_repr' {α} {i} (x : F.obj α i) : abs F α (repr F α x) = x :=
show (repr F α ≫ abs F α) x = x, by rw abs_repr; refl

theorem abs_map' {α β : fam I} (f : α ⟶ β) {i} {x : (P F).obj α i} : abs _ _ ((P F).map f x) = F.map f (abs F α x) :=
show ((P F).map f ≫ abs _ _) x = (abs _ _ ≫ F.map f) x, by rw abs_map


-- theorem id_map {α : typevec n} (x : F α) : typevec.id <$$> x = x :=
-- by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map], reflexivity }

-- theorem comp_map {α β γ : typevec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α) :
--   (g ⊚ f) <$$> x = g <$$> f <$$> x :=
-- by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map, ←abs_map, ←abs_map], reflexivity }

-- instance is_lawful_mvfunctor : mvfunctor.is_lawful F :=
-- { id_map := @id_map n F _ _,
--   comp_map := @comp_map n F _ _ }

-- def mk_B {X : fam J} (P : mvpfunctor I J) (a : X ⟶ P.A) (α : fam I) : Sort* :=
-- Π (i : J) (x : X i), P.B i (a x) ⟶ α

-- def mk_obj {α : fam I} {X : fam J} : Π (P : mvpfunctor I J) (a : X ⟶ P.A), mk_B P a α → (X ⟶ P.obj α)
-- | P a f i x := ⟨a x,f _ x⟩

-- def P_A (α) : Π (P : mvpfunctor I J), P.obj α ⟶ P.A
-- | P i x := x.1

-- def P_B {α} : Π (P : mvpfunctor I J), mk_B P (P_A α P) α
-- | P i ⟨a,f⟩ j b := f b

-- include q
-- set_option pp.implicit true
/- Lifting predicates and relations -/

theorem liftp_iff {α : fam I} {X : fam J} (p : Π i, α i → Prop) (x : X ⟶ F.obj α) :
  liftp p x ↔ ∀ j (y : X j), ∃ a f, x y = abs F α ⟨a,f⟩ ∧ ∀ i a, p i (f a) :=
begin
  split,
  { rintros ⟨y, hy⟩ j z, cases h : repr F _ (y z) with a f,
    use [a,f ≫ fam.subtype.val _], split,
    { rw [← pfunctor.map_eq, ← h, abs_map', abs_repr', ← hy], reflexivity },
    intros i j, apply (f j).property },
  rintros f,
  mk_constructive f,
  let g : X ⟶ (P F).obj (fam.subtype p),
  { intros i y, rcases f i y with ⟨a,g,h,h'⟩,
    refine ⟨a,_⟩, intros k b, refine ⟨g b,h' _ _⟩, },
  have h : g ≫ (P F).map (fam.subtype.val _) ≫ abs F _ = x,
  { dsimp [g], ext : 2, simp,
    rcases (f x_1 x_2) with ⟨a,g,h,h'⟩, simp [h],
    dsimp [pfunctor.map,pfunctor.apply], refl },
  refine ⟨g ≫ abs F _, _⟩,
  rw [category_theory.category.assoc,← abs_map,h],
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
