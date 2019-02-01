/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Tuples of types, and their categorical structure.

Features:

`typevec n`   : n-tuples of types
`α ⟹ β`      : n-tuples of maps
`f ⊚ g`       : composition
`mvfunctor n` : the type class of multivariate functors
`f <$$> x`    : notation for map

Also, support functions for operating with n-tuples of types, such as:

`append1 α β`    : append type `β` to n-tuple `α` to obtain an (n+1)-tuple
`drop α`         : drops the last element of an (n+1)-tuple
`last α`         : returns the last element of an (n+1)-tuple
`append_fun f g` : appends a function g to an n-tuple of functions
`drop_fun f`     : drops the last function from an n+1-tuple
`last_fun f`     : returns the last function of a tuple.

Since e.g. `append1 α.drop α.last` is propositionally equal to `α` but not definitionally equal
to it, we need lots of support functions and lemmas to mediate between constructions.
-/
import .pfunctor

/-
n-tuples of types, as a category
-/

universes u v w

def typevec (n : ℕ) := fin n → Type*

namespace typevec

variable {n : ℕ}

def arrow (α β : typevec n) := Π i : fin n, α i → β i

infixl ` ⟹ `:40 := arrow

def id {α : typevec n} : α ⟹ α := λ i x, x

def comp {α β γ : typevec n} (g : β ⟹ γ) (f : α ⟹ β) : α ⟹ γ :=
λ i x, g i (f i x)

infixr ` ⊚ `:80 := typevec.comp   -- type as \oo

@[simp] theorem id_comp {α β : typevec n} (f : α ⟹ β) : id ⊚ f = f :=
rfl

@[simp] theorem comp_id {α β : typevec n} (f : α ⟹ β) : f ⊚ id = f :=
rfl

theorem comp_assoc {α β γ δ : typevec n} (h : γ ⟹ δ) (g : β ⟹ γ) (f : α ⟹ β) :
  (h ⊚ g) ⊚ f = h ⊚ g ⊚ f := rfl

end typevec

class mvfunctor {n : ℕ} (F : typevec n → Type*) :=
(map : Π {α β : typevec n}, (α ⟹ β) → (F α → F β))

infixr ` <$$> `:100 := mvfunctor.map

class is_lawful_mvfunctor {n : ℕ} (F : typevec n → Type*) [mvfunctor F] : Prop :=
(mv_id_map       : Π {α : typevec n} (x : F α), typevec.id <$$> x = x)
(mv_comp_map     : Π {α β γ : typevec n} (g : α ⟹ β) (h : β ⟹ γ) (x : F α),
                    (h ⊚ g) <$$> x = h <$$> g <$$> x)

export is_lawful_mvfunctor (mv_id_map mv_comp_map)
attribute [simp] mv_id_map

section
variables {n : ℕ} {α β γ : typevec.{u} n}
  {F : typevec.{u} n → Type v} [mvfunctor F] [is_lawful_mvfunctor F]

@[simp]
lemma mv_id_map' (x : F α) :
  (λ i a, a) <$$> x = x :=
mv_id_map n x

lemma mv_map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) :
  h <$$> g <$$> x = (h ⊚ g) <$$> x :=
eq.symm $ mv_comp_map _ _ _

end
/-
Support for extending a typevec by one element.
-/

namespace eq

theorem mp_mpr {α β : Type*} (h : α = β) (x : β) :
  eq.mp h (eq.mpr h x) = x :=
by induction h; reflexivity

theorem mpr_mp {α β : Type*} (h : α = β) (x : α) :
  eq.mpr h (eq.mp h x) = x :=
by induction h; reflexivity

end eq

namespace fin

def succ_cases {n : ℕ} (i : fin (n + 1)) : psum {j : fin n // i = j.cast_succ} (i = fin.last n) :=
begin
  cases i with i h,
  by_cases h' : i < n,
  { left, refine ⟨⟨i, h'⟩, _⟩, apply eq_of_veq, reflexivity },
  right, apply eq_of_veq,
  show i = n, from le_antisymm (nat.le_of_lt_succ h) (le_of_not_lt h')
end

def succ_rec' {n : ℕ} {β : fin (n + 1) → Type*}
  (f : Π i : fin n, β i.cast_succ) (a : β (fin.last n)) : Π i : fin (n + 1), β i
| ⟨i, h⟩ := if h' : i < n then
              have cast_succ ⟨i, h'⟩ = ⟨i, h⟩, from fin.eq_of_veq rfl,
              by rw ←this; exact f ⟨i, h'⟩
            else
              have fin.last n = ⟨i, h⟩,
                from fin.eq_of_veq (le_antisymm (le_of_not_lt h') (nat.le_of_lt_succ h)),
              by rw ←this; exact a

@[simp] theorem succ_rec'_cast_succ {n : ℕ} {β : fin (n + 1) → Type*}
    (f : Π i : fin n, β i.cast_succ) (a : β (fin.last n)) (i : fin n) :
  succ_rec' f a i.cast_succ = f i :=
begin
  cases i with i h,
  change succ_rec' f a ⟨i, _⟩ = _,
  dsimp [succ_rec'], rw dif_pos h,
  reflexivity
end

@[simp] theorem succ_rec'_last {n : ℕ} {β : fin (n + 1) → Type*}
    (f : Π i : fin n, β i.cast_succ) (a : β (fin.last n)) :
  succ_rec' f a (fin.last n) = a :=
begin
  change succ_rec' f a ⟨n, _⟩ = _,
  dsimp [succ_rec'], rw dif_neg (lt_irrefl n),
  reflexivity
end

end fin

namespace typevec

variable {n : ℕ}

def append1 (α : typevec n) (β : Type*) : typevec (n+1) :=
fin.succ_rec' α β

def drop (α : typevec (n+1)) : typevec n := λ i, α i.cast_succ

def last (α : typevec (n+1)) : Type* := α (fin.last n)

theorem drop_append1 {α : typevec n} {β : Type*} {i : fin n} : drop (append1 α β) i = α i :=
fin.succ_rec'_cast_succ _ _ _

theorem last_append1 {α : typevec n} {β : Type*} : last (append1 α β) = β :=
fin.succ_rec'_last _ _

def to_drop_append {α : typevec n} {β : Type*} : α ⟹ drop (append1 α β) :=
λ i, eq.mpr drop_append1

def from_drop_append {α : typevec n} {β : Type*} : drop (append1 α β) ⟹ α :=
λ i, eq.mp drop_append1

@[simp] theorem to_drop_append_from_drop_append {α : typevec n} {β : Type*} {i : fin n}
  (x : drop (append1 α β) i) :
to_drop_append i (from_drop_append i x) = x := eq.mpr_mp _ _

@[simp] theorem from_drop_append_to_drop_append {α : typevec n} {β : Type*} {i : fin n} (x : α i) :
from_drop_append i (@to_drop_append n α β i x) = x := eq.mp_mpr _ _

def to_last_append {α : typevec n} {β : Type*} : β → last (append1 α β) :=
eq.mpr last_append1

def from_last_append {α : typevec n} {β : Type*} : last (append1 α β) → β :=
eq.mp last_append1

@[simp] theorem to_last_append_from_last_append {α : typevec n} {β : Type*} (x : last (append1 α β)) :
to_last_append (from_last_append x) = x := eq.mpr_mp _ _

@[simp] theorem from_last_append_to_last_append {α : typevec n} {β : Type*} (x : β) :
from_last_append (@to_last_append n α β x) = x := eq.mpr_mp _ _

theorem append1_drop_last {α : typevec (n+1)} {i : fin (n+1)} : append1 (drop α) (last α) i = α i :=
by rw [append1, drop, last]; rcases i.succ_cases with ⟨j, ieq⟩ | ieq; rw ieq; simp

def to_append1_drop_last {α : typevec (n+1)} : α ⟹ append1 (drop α) (last α) :=
λ i, eq.mpr append1_drop_last

def from_append1_drop_last {α : typevec (n+1)} : append1 (drop α) (last α) ⟹ α :=
λ i, eq.mp append1_drop_last

@[simp] theorem to_append1_drop_last_from_append1_drop_last {α : typevec (n+1)} {i : fin (n+1)}
    (x : append1 (drop α) (last α) i) :
  to_append1_drop_last i (from_append1_drop_last i x) = x := eq.mp_mpr _ _

@[simp] theorem from_append1_drop_last_to_append1_drop_last {α : typevec (n+1)} {i : fin (n+1)}
    (x : α i) :
  from_append1_drop_last i (to_append1_drop_last i x) = x := eq.mpr_mp _ _

def append_fun {α α' : typevec n} {β β' : Type*}
  (f : α ⟹ α') (g : β → β') : append1 α β ⟹ append1 α' β' :=
fin.succ_rec' (to_drop_append ⊚ f ⊚ from_drop_append) (to_last_append ∘ g ∘ from_last_append)

def drop_fun {α β : typevec (n+1)} (f : α ⟹ β) : drop α ⟹ drop β :=
λ i, f i.cast_succ

def last_fun {α β : typevec (n+1)} (f : α ⟹ β) : last α → last β :=
f (fin.last n)

theorem eq_of_drop_last_eq {α β : typevec (n+1)} (f g : α ⟹ β)
  (h₀ : ∀ j, drop_fun f j = drop_fun g j) (h₁ : last_fun f = last_fun g) : f = g :=
begin
  ext1 i; rcases i.succ_cases with ⟨j, ieq⟩ | ieq; rw ieq,
  { exact h₀ j },
  exact h₁
end

theorem drop_fun_append_fun {α α' : typevec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
  drop_fun (append_fun f g) = to_drop_append ⊚ f ⊚ from_drop_append :=
by ext1 i; dsimp only [drop_fun, append_fun]; rw [fin.succ_rec'_cast_succ]

theorem last_fun_append_fun {α α' : typevec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
  last_fun (append_fun f g) = to_last_append ∘ g ∘ from_last_append :=
by ext1 i; dsimp only [last_fun, append_fun]; rw [fin.succ_rec'_last]

def append_fun_comp {α₀ α₁ α₂ : typevec n} {β₀ β₁ β₂ : Type*}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
  append_fun (f₁ ⊚ f₀) (g₁ ∘ g₀) = append_fun f₁ g₁ ⊚ append_fun f₀ g₀ :=
by ext1 i; rcases i.succ_cases with ⟨j, ieq⟩ | ieq; rw ieq;
    simp [append_fun, function.comp, typevec.comp]

theorem drop_fun_comp {α₀ α₁ α₂ : typevec (n+1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
  drop_fun (f₁ ⊚ f₀) = drop_fun f₁ ⊚ drop_fun f₀ := rfl

theorem last_fun_comp {α₀ α₁ α₂ : typevec (n+1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
  last_fun (f₁ ⊚ f₀) = last_fun f₁ ∘ last_fun f₀ := rfl

theorem drop_fun_to_append1_drop_last {α : typevec (n+1)} :
  drop_fun (@to_append1_drop_last n α) = to_drop_append := rfl

theorem last_fun_to_append1_drop_last {α : typevec (n+1)} :
  last_fun (@to_append1_drop_last n α) = to_last_append := rfl

theorem append_fun_aux {γ : typevec (n+1)} {α : typevec n} {β : Type*} (f : γ ⟹ append1 α β) :
  append_fun (from_drop_append ⊚ drop_fun f)
      (from_last_append ∘ last_fun f) ⊚ to_append1_drop_last = f :=
begin
  ext1 i, rcases i.succ_cases with ⟨j, ieq⟩ | ieq; rw ieq;
    simp [append_fun, function.comp, typevec.comp]; ext x; congr; apply eq.mp_mpr
end

theorem append_fun_id_id {α : typevec n} {β : Type*} :
  append_fun (@id n α) (@_root_.id β) = id :=
by ext1 i; rcases i.succ_cases with ⟨j, ieq⟩ | ieq; rw ieq; ext x;
     simp [append_fun, typevec.comp, id]

end typevec
