
import category_theory.category category_theory.types

universes u v w

open category_theory

@[reducible]
def fam (I : Type u) := I → Type u

namespace fam

def drop {I α : Type u} : fam (I ⊕ α) → fam I :=
λ x i, x (sum.inl i)

def last {I α : Type u} : fam (I ⊕ α) → fam α :=
λ x i, x (sum.inr i)

def append1 {I α : Type u} (f : fam I) (g : fam α) : fam (I ⊕ α)
| (sum.inl i) := f i
| (sum.inr i) := g i

end fam

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

namespace fam

variables {I J : Type u}

def split_fun {α β : fam (I⊕J)} :
  Π (f : drop α ⟶ drop β) (g : last α ⟶ last β), α ⟶ β
| f g (sum.inl i) x := f x
| f g (sum.inr i) x := g x

def append_fun {α β : fam I} {α' β' : fam J} (f : α ⟶ β) (g : α' ⟶ β') : (α.append1 α' ⟶ β.append1 β') :=
split_fun f g

lemma split_fun_comp {α β γ : fam (I⊕J)}
  (f : drop α ⟶ drop β) (g : drop β ⟶ drop γ) (f' : last α ⟶ last β) (g' : last β ⟶ last γ) :
  split_fun (f ≫ g) (f' ≫ g') = split_fun f f' ≫ split_fun g g' :=
by ext (x|x) : 1; ext; refl

lemma split_fun_comp_right {α : fam (I⊕J)} {β γ : fam J} {γ' : fam I}
  (f : drop α ⟶ γ')
  (f' : last α ⟶ β) (g' : β ⟶ γ) :
  (split_fun f (f' ≫ g') : α ⟶ γ'.append1 γ) =
  (split_fun f f' : α ⟶ γ'.append1 β) ≫ split_fun (𝟙 _) g' :=
by rw [← split_fun_comp,category.comp_id]


def drop_fun {α β : fam (I⊕J)} : Π (f : α ⟶ β), drop α ⟶ drop β
| f i x := f x

def last_fun {α β : fam (I⊕J)} : Π (f : α ⟶ β), last α ⟶ last β
| f i x := f x

theorem eq_of_drop_last_eq {α β : fam (I⊕J)} {f g : α ⟶ β}
  (h₀ : ∀ j (x : α (sum.inl j)), drop_fun f x = drop_fun g x) (h₁ : last_fun f = last_fun g) : f = g :=
by { ext1 (i|j); ext1 x, apply h₀, apply congr_fun (congr_fun h₁ j), }
-- by ext1 i; rcases i with ⟨j, ieq⟩ | ieq; [apply h₀, apply h₁]

theorem split_drop_fun_last_fun {α α' : fam (I⊕J)} (f : α ⟶ α') :
  split_fun (drop_fun f) (last_fun f) = f :=
eq_of_drop_last_eq (λ _ _, rfl) (funext $ λ _, funext $ λ _, rfl)

end fam
