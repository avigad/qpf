/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Multivariate polynomial functors.

Note: eventually the W and M constructions as multivariate polynomial functors will go here.
-/
import .mvfunctor
universe u

/-
multivariate polynomial functors
-/

structure mvpfunctor (n : ℕ) :=
(A : Type.{u}) (B : A → typevec.{u} n)

namespace mvpfunctor

variables {n : ℕ} (P : mvpfunctor.{u} n)

def apply (α : typevec.{u} n) : Type* := Σ a : P.A, P.B a ⟹ α

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

end mvpfunctor

