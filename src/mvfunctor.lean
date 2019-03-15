/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Mario Carneiro

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
to it, we need support functions and lemmas to mediate between constructions.
-/
import pfunctor
import for_mathlib

/-
n-tuples of types, as a category
-/

universes u v w

inductive fin' : ℕ → Type
| raise {n : ℕ} : fin' n → fin' n.succ
| last {n : ℕ} : fin' n.succ

def fin'.elim0 {α} : fin' 0 → α .

def typevec (n : ℕ) := fin' n → Type*

namespace typevec

variable {n : ℕ}

def arrow (α β : typevec n) := Π i : fin' n, α i → β i

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

namespace mvfunctor

variables {n : ℕ} {α β γ : typevec.{u} n} {F : typevec.{u} n → Type v} [mvfunctor F]

def liftp {α : typevec n} (p : Π i, α i → Prop) : F α → Prop :=
λ x, ∃ u : F (λ i, subtype (p i)), (λ i, @subtype.val _ (p i)) <$$> u = x

def liftr {α : typevec n} (r : Π {i}, α i → α i → Prop) : F α → F α → Prop :=
λ x y, ∃ u : F (λ i, {p : α i × α i // r p.fst p.snd}),
  (λ i (t : {p : α i × α i // r p.fst p.snd}), t.val.fst) <$$> u = x ∧
  (λ i (t : {p : α i × α i // r p.fst p.snd}), t.val.snd) <$$> u = y

def supp {α : typevec n} (x : F α) (i : fin' n) : set (α i) :=
{ y : α i | ∀ {p}, liftp p x → p i y }

theorem of_mem_supp {α : typevec n} {x : F α} {p : Π ⦃i⦄, α i → Prop} (h : liftp p x) (i : fin' n):
  ∀ y ∈ supp x i, p y :=
λ y hy, hy h

end mvfunctor

namespace mvfunctor

class is_lawful {n : ℕ} (F : typevec n → Type*) [mvfunctor F] : Prop :=
(id_map       : Π {α : typevec n} (x : F α), typevec.id <$$> x = x)
(comp_map     : Π {α β γ : typevec n} (g : α ⟹ β) (h : β ⟹ γ) (x : F α),
                    (h ⊚ g) <$$> x = h <$$> g <$$> x)

export is_lawful (id_map comp_map)
attribute [simp] id_map

variables {n : ℕ} {α β γ : typevec.{u} n}
variables {F : typevec.{u} n → Type v} [mvfunctor F] [is_lawful F]

@[simp]
lemma id_map' (x : F α) :
  (λ i a, a) <$$> x = x :=
id_map n x

lemma map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) :
  h <$$> g <$$> x = (h ⊚ g) <$$> x :=
eq.symm $ comp_map _ _ _

end mvfunctor
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

-- def succ_rec' {n : ℕ} {β : fin (n + 1) → Sort*}
--   (f : Π i : fin n, β i.cast_succ) (a : β (fin.last n)) : Π i : fin (n + 1), β i
-- | ⟨i, h⟩ := if h' : i < n then
--               have cast_succ ⟨i, h'⟩ = ⟨i, h⟩, from fin.eq_of_veq rfl,
--               by rw ←this; exact f ⟨i, h'⟩
--             else
--               have fin.last n = ⟨i, h⟩,
--                 from fin.eq_of_veq (le_antisymm (le_of_not_lt h') (nat.le_of_lt_succ h)),
--               by rw ←this; exact a

-- @[simp] theorem succ_rec'_cast_succ {n : ℕ} {β : fin (n + 1) → Type*}
--     (f : Π i : fin n, β i.cast_succ) (a : β (fin.last n)) (i : fin n) :
--   succ_rec' f a i.cast_succ = f i :=
-- begin
--   cases i with i h,
--   change succ_rec' f a ⟨i, _⟩ = _,
--   dsimp [succ_rec'], rw dif_pos h,
--   reflexivity
-- end

-- @[simp] theorem succ_rec'_last {n : ℕ} {β : fin (n + 1) → Type*}
--     (f : Π i : fin n, β i.cast_succ) (a : β (fin.last n)) :
--   succ_rec' f a (fin.last n) = a :=
-- begin
--   change succ_rec' f a ⟨n, _⟩ = _,
--   dsimp [succ_rec'], rw dif_neg (lt_irrefl n),
--   reflexivity
-- end

end fin

namespace typevec

variable {n : ℕ}

def append1 (α : typevec n) (β : Type*) : typevec (n+1)
| (fin'.raise i) := α i
| fin'.last      := β

def drop (α : typevec (n+1)) : typevec n := λ i, α i.raise

def last (α : typevec (n+1)) : Type* := α fin'.last

theorem drop_append1 {α : typevec n} {β : Type*} {i : fin' n} : drop (append1 α β) i = α i := rfl

theorem drop_append1' {α : typevec n} {β : Type*} : drop (append1 α β) = α :=
by ext; apply drop_append1

theorem last_append1 {α : typevec n} {β : Type*} : last (append1 α β) = β := rfl

@[simp]
theorem append1_drop_last (α : typevec (n+1)) : append1 (drop α) (last α) = α :=
funext $ λ i, by cases i; refl

@[elab_as_eliminator] def append1_cases
  {C : typevec (n+1) → Sort u} (H : ∀ α β, C (append1 α β)) (γ) : C γ :=
by rw [← @append1_drop_last _ γ]; apply H

@[simp] theorem append1_cases_append1 {C : typevec (n+1) → Sort u}
  (H : ∀ α β, C (append1 α β)) (α β) :
  @append1_cases _ C H (append1 α β) = H α β := rfl

def split_fun {α α' : typevec (n+1)}
  (f : drop α ⟹ drop α') (g : last α → last α') : α ⟹ α'
| (fin'.raise i) := f i
| fin'.last      := g

def append_fun {α α' : typevec n} {β β' : Type*}
  (f : α ⟹ α') (g : β → β') : append1 α β ⟹ append1 α' β' := split_fun f g

def drop_fun {α β : typevec (n+1)} (f : α ⟹ β) : drop α ⟹ drop β :=
λ i, f i.raise

def last_fun {α β : typevec (n+1)} (f : α ⟹ β) : last α → last β :=
f fin'.last

theorem eq_of_drop_last_eq {α β : typevec (n+1)} {f g : α ⟹ β}
  (h₀ : ∀ j, drop_fun f j = drop_fun g j) (h₁ : last_fun f = last_fun g) : f = g :=
by ext1 i; rcases i with ⟨j, ieq⟩ | ieq; [apply h₀, apply h₁]

@[simp] theorem drop_fun_split_fun {α α' : typevec (n+1)}
  (f : drop α ⟹ drop α') (g : last α → last α') :
  drop_fun (split_fun f g) = f := rfl

-- @[simp]
-- theorem append1_drop_last' {α : typevec (n+1)} : append1 (drop α) (last α) = α :=
-- funext $ λ i, append1_drop_last _

def arrow.mp {α β : typevec n} (h : α = β) : α ⟹ β
| i := eq.mp (congr_fun h _)

def arrow.mpr {α β : typevec n} (h : α = β) : β ⟹ α
| i := eq.mpr (congr_fun h _)

def to_append1_drop_last {α : typevec (n+1)} : α ⟹ append1 (drop α) (last α) :=
arrow.mpr (append1_drop_last _)

-- def from_append1_drop_last {α : typevec (n+1)} : α ⟹ append1 (drop α) (last α) :=
-- arrow.mpr (append1_drop_last _)

@[simp] theorem last_fun_split_fun {α α' : typevec (n+1)}
  (f : drop α ⟹ drop α') (g : last α → last α') :
  last_fun (split_fun f g) = g := rfl

@[simp] theorem drop_fun_append_fun {α α' : typevec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
  drop_fun (append_fun f g) = f := rfl

@[simp] theorem last_fun_append_fun {α α' : typevec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
  last_fun (append_fun f g) = g := rfl

theorem split_drop_fun_last_fun {α α' : typevec (n+1)} (f : α ⟹ α') :
  split_fun (drop_fun f) (last_fun f) = f :=
eq_of_drop_last_eq (λ _, rfl) rfl

theorem split_fun_inj
  {α α' : typevec (n+1)} {f f' : drop α ⟹ drop α'} {g g' : last α → last α'}
  (H : split_fun f g = split_fun f' g') : f = f' ∧ g = g' :=
by rw [← drop_fun_split_fun f g, H, ← last_fun_split_fun f g, H]; simp

def nil_fun : fin'.elim0 ⟹ fin'.elim0 :=
λ i, fin'.elim0 i

-- def drop_fun {α β : typevec (n+1)} (f : α ⟹ β) : drop α ⟹ drop β :=
-- λ i, f _

theorem append_fun_inj {α α' : typevec n} {β β' : Type*} {f f' : α ⟹ α'} {g g' : β → β'} :
  append_fun f g = append_fun f' g' →  f = f' ∧ g = g' :=
split_fun_inj

theorem split_fun_comp {α₀ α₁ α₂ : typevec (n+1)}
    (f₀ : drop α₀ ⟹ drop α₁) (f₁ : drop α₁ ⟹ drop α₂)
    (g₀ : last α₀ → last α₁) (g₁ : last α₁ → last α₂) :
  split_fun (f₁ ⊚ f₀) (g₁ ∘ g₀) = split_fun f₁ g₁ ⊚ split_fun f₀ g₀ :=
eq_of_drop_last_eq (λ _, rfl) rfl

-- theorem eq_of_drop_last_eq {α β : typevec (n+1)} (f g : α ⟹ β)
--   (h₀ : ∀ j, drop_fun f j = drop_fun g j) (h₁ : last_fun f = last_fun g) : f = g :=
-- begin
--   ext1 i; rcases i.succ_cases with ⟨j, ieq⟩ | ieq; rw ieq,
--   { exact h₀ j },
--   exact h₁
-- end

-- @[simp]
-- theorem drop_fun_append_fun {α α' : typevec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
--   drop_fun (append_fun f g) = to_drop_append ⊚ f ⊚ from_drop_append :=
-- by ext1 i; dsimp only [drop_fun, append_fun]; rw [fin.succ_rec'_cast_succ]

-- @[simp]
-- theorem last_fun_append_fun {α α' : typevec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
--   last_fun (append_fun f g) = to_last_append ∘ g ∘ from_last_append :=
-- by ext1 i; dsimp only [last_fun, append_fun]; rw [fin.succ_rec'_last]

lemma append_fun_comp {α₀ α₁ α₂ : typevec n} {β₀ β₁ β₂ : Type*}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
  append_fun (f₁ ⊚ f₀) (g₁ ∘ g₀) = append_fun f₁ g₁ ⊚ append_fun f₀ g₀ :=
eq_of_drop_last_eq (λ _, rfl) rfl

theorem append_fun_comp_id {α : typevec n} {β₀ β₁ β₂ : Type*}
    (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
  append_fun (@id _ α) (g₁ ∘ g₀) = append_fun id g₁ ⊚ append_fun id g₀ :=
eq_of_drop_last_eq (λ _, rfl) rfl

-- theorem append_fun_aux {γ : typevec (n+1)} {α : typevec n} {β : Type*} (f : γ ⟹ append1 α β) :
--   append_fun (from_drop_append ⊚ drop_fun f)
--       (from_last_append ∘ last_fun f) ⊚ to_append1_drop_last = f :=
-- begin
--   ext1 i, rcases i.succ_cases with ⟨j, ieq⟩ | ieq; rw ieq;
--     simp [append_fun, function.comp, typevec.comp]; ext x; congr; apply eq.mp_mpr
-- end

-- theorem append_fun_id_id {α : typevec n} {β : Type*} :
--   append_fun (@id n α) (@_root_.id β) = id :=
-- by ext1 i; rcases i.succ_cases with ⟨j, ieq⟩ | ieq; rw ieq; ext x;
--      simp [append_fun, typevec.comp, id]

-- @[extensionality]
-- lemma arrow_ext' {α₀ β₀ : typevec $ n+1}
--     {f₀ f₁ : α₀ ⟹ β₀}
--     (h₀ : drop_fun f₀ = drop_fun f₁)
--     (h₁ : last_fun f₀ = last_fun f₁) :
--   f₀ = f₁ :=
-- by { ext i : 1,
--      induction i, apply fin.succ_rec' _ _ i; intros, apply congr_fun h₀ i_1, apply h₁ }

-- @[extensionality]
-- lemma arrow_ext {α₀ α₁ β₀ β₁ : typevec $ n+1}
--     {f₀ : α₀ ⟹ β₀} {f₁ : α₁ ⟹ β₁}
--     (h₀ : α₀ = α₁)
--     (h₁ : β₀ = β₁)
--     (h₂ : drop_fun f₀ == drop_fun f₁)
--     (h₃ : last_fun f₀ == last_fun f₁) :
--   f₀ == f₁ :=
-- by { subst h₀, subst β₁, simp, ext : 1; apply eq_of_heq,
--      induction n, }

@[simp]
theorem drop_fun_comp {α₀ α₁ α₂ : typevec (n+1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
  drop_fun (f₁ ⊚ f₀) = drop_fun f₁ ⊚ drop_fun f₀ := rfl

@[simp]
theorem last_fun_comp {α₀ α₁ α₂ : typevec (n+1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
  last_fun (f₁ ⊚ f₀) = last_fun f₁ ∘ last_fun f₀ := rfl

theorem append_fun_aux {α α' : typevec n} {β β' : Type*}
  (f : append1 α β ⟹ append1 α' β') : append_fun (drop_fun f) (last_fun f) = f :=
eq_of_drop_last_eq (λ _, rfl) rfl

-- @[simp]
-- theorem drop_fun_to_append1_drop_last {α : typevec (n+1)} :
--   drop_fun (@to_append1_drop_last n α) = to_drop_append := rfl

theorem append_fun_id_id {α : typevec n} {β : Type*} :
  append_fun (@id n α) (@_root_.id β) = id :=
eq_of_drop_last_eq (λ _, rfl) rfl

-- @[simp]
-- theorem drop_fun_from_append1_drop_last {α : typevec (n+1)} :
--   drop_fun (@from_append1_drop_last n α) = from_drop_append := by ext; refl

-- @[simp]
-- theorem last_fun_to_append1_drop_last {α : typevec (n+1)} :
--   last_fun (@to_append1_drop_last n α) = to_last_append := rfl

-- @[simp]
-- theorem last_fun_from_append1_drop_last {α : typevec (n+1)} :
--   last_fun (@from_append1_drop_last n α) = from_last_append := rfl

-- lemma append_fun_drop_fun_last_fun {α₀ α₁ : typevec $ n+1}
--     (f₀ : α₀ ⟹ α₁) :
--   append_fun (drop_fun f₀) (last_fun f₀) = to_append1_drop_last ⊚ f₀ ⊚ _ :=
-- by { ext; simp, }

-- inductive ind : ℕ → Type.{u+1}
-- | nil : ind 0
-- | cons {n : ℕ} : Type u → ind n → ind (n + 1)

-- def of_ind : Π {n}, ind.{u} n → typevec.{u} n
-- | ._ ind.nil := fin.elim0
-- | ._ (ind.cons t ts) := append1 (of_ind ts) t

-- def to_ind : Π {n}, typevec.{u} n → ind.{u} n
-- | 0 _ := ind.nil
-- | (n+1) f := ind.cons (last f) (to_ind (drop f))

-- lemma of_ind_to_ind (v : typevec.{u} n) : of_ind (to_ind v) = v :=
-- by { induction n; ext; simp! [*,append1_drop_last], apply fin'.elim0 x }

-- lemma to_ind_of_ind (v : ind.{u} n) : to_ind (of_ind v) = v :=
-- by induction v; simp [of_ind,to_ind,last_append1,drop_append1',*]

instance subsingleton0 : subsingleton (typevec 0) :=
⟨ λ a b, funext $ λ a, fin'.elim0 a  ⟩

run_cmd mk_simp_attr `typevec
-- attribute [typevec]

local prefix `♯`:0 := cast (by try { simp }; congr' 1; try { simp })

def typevec_cases_nil {β : typevec 0 → Sort*} (f : β fin'.elim0) :
  Π v, β v :=
λ v, ♯ f

def typevec_cases_cons (n : ℕ) {β : typevec (n+1) → Sort*} (f : Π t (v : typevec n), β (typevec.append1 v t)) :
  Π v, β v :=
λ v, ♯ f v.last v.drop

-- lemma typevec_cases_cons_append (n : ℕ) {β : typevec (n+1) → Sort*} (f : Π t (v : typevec n), β (typevec.append1 v t))

-- def typevec_cases {n : ℕ} {β : typevec n → Sort*} (f : Π v : typevec.ind n, β (typevec.of_ind v)) :
--   Π v, β v :=
-- λ v,♯ f v.to_ind

open typevec

def map0 : fin'.elim0 ⟹ fin'.elim0 | i := fin'.elim0 i

def typevec_cases_nil₃ {β : Π v v' : typevec 0, v ⟹ v' → Sort*} (f : β fin'.elim0 fin'.elim0 map0) :
  Π v v' f, β v v' f :=
λ v v' fs,
begin
  refine cast _ f; congr; ext; try { intros; exact fin'.elim0 ‹ fin' 0 ›  }; refl
end

def typevec_cases_cons₃ (n : ℕ) {β : Π v v' : typevec (n+1), v ⟹ v' → Sort*}
  (f : Π t t' (f : t → t') (v v' : typevec n) (fs : v ⟹ v'), β (append1 v t) (append1 v' t') (append_fun fs f)) :
  Π v v' f, β v v' f :=
λ v v' fs,
begin
  refine cast _ (f v.last v'.last (last_fun fs) v.drop v'.drop (drop_fun fs)),
  congr' 1, repeat { simp  }, ext : 1; simp, admit,
end

def typevec_cases_cons₂ (n : ℕ) (t t' : Type*) (v v' : typevec (n)) {β : (append1 v t) ⟹ (append1 v' t') → Sort*}
  (f : Π (f : t → t') (fs : v ⟹ v'), β (append_fun fs f)) :
  Π f, β f := sorry

/- for lifting predicates and relations -/

/-- `pred_last α p x` predicates `p` of the last element of `x : α.append1 β`. -/
def pred_last (α : typevec n) {β : Type*} (p : β → Prop) : Π ⦃i⦄, (α.append1 β) i → Prop
| (fin'.raise i) := λ x, true
| fin'.last      := p

/-- `rel_last α r x y` says that `p` the last elements of `x y : α.append1 β` are related by `r` and all the other elements are equal. -/
def rel_last (α : typevec n) {β γ : Type*} (r : β → γ → Prop) :
  Π ⦃i⦄, (α.append1 β) i → (α.append1 γ) i → Prop
| (fin'.raise i) := eq
| fin'.last      := r

end typevec
