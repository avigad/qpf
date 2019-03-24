/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Polynomial functors. Also expresses the W-type construction as a polynomial functor.
(For the M-type construction, see Mtype.lean.)
-/
import tactic.interactive data.multiset
universe u

/-
A polynomial functor `P` is given by a type `A` and a family `B` of types over `A`. `P` maps
any type `α` to a new type `P.apply α`.

An element of `P.apply α` is a pair `⟨a, f⟩`, where `a` is an element of a type `A` and
`f : B a → α`. Think of `a` as the shape of the object and `f` as an index to the relevant
elements of `α`.
-/

structure pfunctor :=
(A : Type u) (B : A → Type u)

namespace pfunctor

variables (P : pfunctor) {α β : Type u}

-- TODO: generalize to psigma?
def apply (α : Type*) := Σ x : P.A, P.B x → α

def map {α β : Type*} (f : α → β) : P.apply α → P.apply β :=
λ ⟨a, g⟩, ⟨a, f ∘ g⟩

instance : functor P.apply := {map := @map P}

theorem map_eq {α β : Type*} (f : α → β) (a : P.A) (g : P.B a → α) :
  @functor.map P.apply _ _ _ f ⟨a, g⟩ = ⟨a, f ∘ g⟩ :=
rfl

theorem id_map {α : Type*} : ∀ x : P.apply α, id <$> x = id x :=
λ ⟨a, b⟩, rfl

theorem comp_map {α β γ : Type*} (f : α → β) (g : β → γ) :
  ∀ x : P.apply α, (g ∘ f) <$> x = g <$> (f <$> x) :=
λ ⟨a, b⟩, rfl

instance : is_lawful_functor P.apply :=
{id_map := @id_map P, comp_map := @comp_map P}

inductive W
| mk (a : P.A) (f : P.B a → W) : W

def W_dest : W P → P.apply (W P)
| ⟨a, f⟩ := ⟨a, f⟩

def W_mk : P.apply (W P) → W P
| ⟨a, f⟩ := ⟨a, f⟩

@[simp] theorem W_dest_W_mk (p : P.apply (W P)) : P.W_dest (P.W_mk p) = p :=
by cases p; reflexivity

@[simp] theorem W_mk_W_dest (p : W P) : P.W_mk (P.W_dest p) = p :=
by cases p; reflexivity

def Idx := Σ x : P.A, P.B x
variables {P}

def apply.iget [decidable_eq P.A] {α} [inhabited α] (x : P.apply α) (i : P.Idx) : α :=
if h : i.1 = x.1
  then x.2 (cast (congr_arg _ h) i.2)
  else default _

@[simp]
lemma fst_map {α β : Type u} (x : P.apply α) (f : α → β) :
  (f <$> x).1 = x.1 := by { cases x; refl }

@[simp]
lemma iget_map [decidable_eq P.A] {α β : Type u} [inhabited α] [inhabited β]
  (x : P.apply α) (f : α → β) (i : P.Idx)
  (h : i.1 = x.1) :
  (f <$> x).iget i = f (x.iget i) :=
by { simp [apply.iget],
     rw [dif_pos h,dif_pos];
     cases x, refl, rw h, refl }

end pfunctor

/-
Composition of polynomial functors.
-/

namespace pfunctor

/-
def comp : pfunctor.{u} → pfunctor.{u} → pfunctor.{u}
| ⟨A₂, B₂⟩ ⟨A₁, B₁⟩ := ⟨Σ a₂ : A₂, B₂ a₂ → A₁, λ ⟨a₂, a₁⟩, Σ u : B₂ a₂, B₁ (a₁ u)⟩
-/

def comp (P₂ P₁ : pfunctor.{u}) : pfunctor.{u} :=
⟨ Σ a₂ : P₂.1, P₂.2 a₂ → P₁.1,
  λ a₂a₁, Σ u : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u) ⟩

def comp.mk (P₂ P₁ : pfunctor.{u}) {α : Type} (x : P₂.apply (P₁.apply α)) : (comp P₂ P₁).apply α :=
⟨ ⟨ x.1, sigma.fst ∘ x.2 ⟩, λ a₂a₁, (x.2 a₂a₁.1).2 a₂a₁.2  ⟩

def comp.get (P₂ P₁ : pfunctor.{u}) {α : Type} (x : (comp P₂ P₁).apply α) : P₂.apply (P₁.apply α) :=
⟨ x.1.1, λ a₂, ⟨x.1.2 a₂, λ a₁, x.2 ⟨a₂,a₁⟩ ⟩ ⟩

end pfunctor

/-
Facts about the general quotient needed to construct final coalgebras.

TODO (Jeremy): move these somewhere.
-/

namespace quot

def factor {α : Type*} (r s: α → α → Prop) (h : ∀ x y, r x y → s x y) :
  quot r → quot s :=
quot.lift (quot.mk s) (λ x y rxy, quot.sound (h x y rxy))

def factor_mk_eq {α : Type*} (r s: α → α → Prop) (h : ∀ x y, r x y → s x y) :
  factor r s h ∘ quot.mk _= quot.mk _ := rfl

end quot
