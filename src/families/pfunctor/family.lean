
import category_theory.category category_theory.types

universes u v w

open category_theory

@[reducible]
def fam (I : Type u) := I → Type u

section pis

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

instance pi.category {α : Type w} : category $ α → C :=
{ hom := λ X Y, Π ⦃i⦄, X i ⟶ Y i,
  id := λ X i, 𝟙 (X i),
  comp := λ X Y Z f g i, @f i ≫ @g i }

end pis

instance fam.category {I : Type u} : category $ fam I :=
pi.category
