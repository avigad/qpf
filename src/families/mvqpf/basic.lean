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

/-
Show that every mvqpf is a lawful mvfunctor.
-/
include q

attribute [simp, reassoc] abs_map abs_repr

theorem abs_repr' {α} {i} (x : F.obj α i) : abs α (repr α x) = x :=
show (repr α ≫ abs α) x = x, by rw abs_repr; refl

theorem abs_map' {α β : fam I} (f : α ⟶ β) {i} {x : (P F).obj α i} : abs _ ((P F).map f x) = F.map f (abs α x) :=
show ((P F).map f ≫ abs _) x = (abs _ ≫ F.map f) x, by rw abs_map

/- Lifting predicates and relations -/

open category_theory

theorem abs_epi {α β : fam I} {X : fam J} (f g : F.obj α ⟶ X)
  (h : abs α ≫ f = abs α ≫ g) : f = g :=
suffices 𝟙 _ ≫ f = g, by rw [← this,category.id_comp],
by rw [← abs_repr,category.assoc,h,← category.assoc,abs_repr,category.id_comp]

theorem repr_mono {α β : fam I} {X : fam J} (f g : X ⟶ F.obj β)
  (h : f ≫ repr β = g ≫ repr β) : f = g :=
suffices f ≫ 𝟙 _ = g, by rw [← this,category.comp_id],
by rw [← abs_repr,← category.assoc,h,category.assoc,abs_repr,category.comp_id]

theorem trade  {α : fam I} {X : fam J} (f : (P F).obj α ⟶ X) (g : F.obj α ⟶ X)
  (h : f = abs α ≫ g) : repr α ≫ f = g :=
by rw [h,← category.assoc,abs_repr,category.id_comp]

open pfunctor (map_eq')

open mvqpf (abs_map)

theorem liftp_iff {α : fam I} {X : fam J} (p : Π i, α i → Prop) (x : X ⟶ F.obj α) :
  liftp p x ↔ ∀ j (y : X j), ∃ a f, x y = abs α ⟨a,f⟩ ∧ ∀ i a, p i (f a) :=
begin
  split,
  { rintros ⟨y, hy⟩ j z, cases h : repr _ (y z) with a f,
    use [a,f ≫ fam.subtype.val], split,
    { rw [← pfunctor.map_eq', ← h, abs_map', abs_repr', ← hy], reflexivity },
    intros i j, apply (f j).property },
  rintros f,
  mk_constructive f,
  let g : X ⟶ (P F).obj (fam.subtype p),
  { intros i y, rcases f i y with ⟨a,g,h,h'⟩,
    refine ⟨a,_⟩, intros k b, refine ⟨g b,h' _ _⟩, },
  have h : g ≫ (P F).map fam.subtype.val ≫ abs _ = x,
  { dsimp [g], ext : 2, simp,
    rcases (f x_1 x_2) with ⟨a,g,h,h'⟩, simp [h],
    erw [← abs_map',map_eq'], refl },
  refine ⟨g ≫ abs _, _⟩,
  rw [category_theory.category.assoc,← abs_map,h],
end

theorem liftr_iff {α β : fam I} {X : fam J} (r : fam.Pred (α ⊗ β))
  (x : X ⟶ F.obj α) (y : X ⟶ F.obj β) :
  liftr r x y ↔ ∀ j (k : X j), ∃ a f₀ f₁, x k = abs _ ⟨a, f₀⟩ ∧ y k = abs _ ⟨a, f₁⟩ ∧ ∀ i a, r i (f₀ a, f₁ a) :=
begin
  split,
  { rintros ⟨y, hy⟩ j z, cases h : repr _ (y z) with a f,
    use [a,f ≫ fam.subtype.val ≫ fam.prod.fst,f ≫ fam.subtype.val ≫ fam.prod.snd], split,
    { rw [← pfunctor.map_eq', ← h, abs_map', abs_repr', ← hy.1], reflexivity },
    split,
    { rw [← pfunctor.map_eq', ← h, abs_map', abs_repr', ← hy.2], reflexivity },
    intros i j, convert (f j).property, simp [fam.prod.fst,fam.prod.snd,fam.subtype.val], },
  rintros f,
  mk_constructive f,
  let g : X ⟶ (P F).obj (fam.subtype r),
  { intros i y, rcases f i y with ⟨a,g,g',h,h',h''⟩,
    refine ⟨a,_⟩, intros k b, refine ⟨(g b,g' b),h'' _ _⟩, },
  have h : g ≫ (P F).map (fam.subtype.val ≫ fam.prod.fst) ≫ abs _ = x,
  { dsimp [g], ext : 2, simp, mk_opaque g,
    rcases (f x_1 x_2) with ⟨a,g,g',h,h',h''⟩, simp [h],
    erw [← abs_map',← abs_map',map_eq'], refl },
  have h' : g ≫ (P F).map (fam.subtype.val ≫ fam.prod.snd) ≫ abs _ = y,
  { dsimp [g], ext : 2, simp,
    rcases (f x_1 x_2) with ⟨a,g,g',h,h',h''⟩, simp [h'],
    erw [← abs_map',← abs_map',map_eq'], refl },
  mk_opaque g,
  refine ⟨g ≫ abs _, _⟩,
  simp only [h.symm,h'.symm,pfunctor.map_comp,abs_map,abs_map_assoc,
    category.assoc,and_self,eq_self_iff_true,category_theory.functor.map_comp],
end
open fam

theorem liftr_iff' {α β : fam I} (r : fam.Pred (α ⊗ β))
  {i : J} (x : unit i ⟶ F.obj α) (y : unit i ⟶ F.obj β) :
  liftr r x y ↔ ∃ a f₀ f₁, x = value i (q.P.obj _) ⟨a, f₀⟩ ≫ abs _ ∧ y = value i (q.P.obj _) ⟨a, f₁⟩ ≫ abs _ ∧ ∀ i a, r i (f₀ a, f₁ a) :=
begin
  rw liftr_iff, split,
  { intros h, rcases h _ unit.rfl with ⟨a,f₀,f₁,hx,hy,hf₀₁⟩, clear h,
    refine ⟨a,f₀,f₁,_,_,hf₀₁⟩; ext _ ⟨ ⟩,
    rw hx, refl, rw hy, refl },
  { rintro ⟨a,f₀,f₁,hx,hy,hf₀₁⟩ _ ⟨ ⟩,
    refine ⟨a,f₀,f₁,_,_,hf₀₁⟩,
    rw hx, refl, rw hy, refl }
end

end mvqpf
