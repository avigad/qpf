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
import for_mathlib

/-
n-tuples of types, as a category
-/

universes u v w

inductive fin' : ℕ → Type
| raise {n : ℕ} : fin' n → fin' n.succ
| last {n : ℕ} : fin' n.succ

def fin'.elim0 {α} : fin' 0 → α .

def typevec' (n : ℕ) := fin' n → Sort*
def typevec (n : ℕ) := typevec'.{u+1} n

namespace typevec

variable {n : ℕ}

def arrow (α β : typevec' n) := Π i : fin' n, α i → β i

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

end fin

namespace typevec

variable {n : ℕ}

def append1 (α : typevec n) (β : Type*) : typevec (n+1)
| (fin'.raise i) := α i
| fin'.last      := β

infixl ` ::: `:67 := append1

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

def split_fun {α α' : typevec' (n+1)}
  (f : drop α ⟹ drop α') (g : last α → last α') : α ⟹ α'
| (fin'.raise i) := f i
| fin'.last      := g

def append_fun {α α' : typevec' n} {β β' : Type*}
  (f : α ⟹ α') (g : β → β') : append1 α β ⟹ append1 α' β' := split_fun f g

infixl ` ::: ` := append_fun

def drop_fun {α β : typevec (n+1)} (f : α ⟹ β) : drop α ⟹ drop β :=
λ i, f i.raise

def last_fun {α β : typevec (n+1)} (f : α ⟹ β) : last α → last β :=
f fin'.last

def nil_fun {α : typevec 0} {β : typevec 0} : α ⟹ β :=
λ i, fin'.elim0 i

theorem eq_of_drop_last_eq {α β : typevec (n+1)} {f g : α ⟹ β}
  (h₀ : ∀ j, drop_fun f j = drop_fun g j) (h₁ : last_fun f = last_fun g) : f = g :=
by ext1 i; rcases i with ⟨j, ieq⟩ | ieq; [apply h₀, apply h₁]

@[simp] theorem drop_fun_split_fun {α α' : typevec (n+1)}
  (f : drop α ⟹ drop α') (g : last α → last α') :
  drop_fun (split_fun f g) = f := rfl

def arrow.mp {α β : typevec n} (h : α = β) : α ⟹ β
| i := eq.mp (congr_fun h _)

def arrow.mpr {α β : typevec n} (h : α = β) : β ⟹ α
| i := eq.mpr (congr_fun h _)

def to_append1_drop_last {α : typevec (n+1)} : α ⟹ drop α ::: last α :=
arrow.mpr (append1_drop_last _)

@[simp] theorem last_fun_split_fun {α α' : typevec (n+1)}
  (f : drop α ⟹ drop α') (g : last α → last α') :
  last_fun (split_fun f g) = g := rfl

@[simp] theorem drop_fun_append_fun {α α' : typevec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
  drop_fun (f ::: g) = f := rfl

@[simp] theorem last_fun_append_fun {α α' : typevec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
  last_fun (f ::: g) = g := rfl

theorem split_drop_fun_last_fun {α α' : typevec (n+1)} (f : α ⟹ α') :
  split_fun (drop_fun f) (last_fun f) = f :=
eq_of_drop_last_eq (λ _, rfl) rfl

theorem split_fun_inj
  {α α' : typevec (n+1)} {f f' : drop α ⟹ drop α'} {g g' : last α → last α'}
  (H : split_fun f g = split_fun f' g') : f = f' ∧ g = g' :=
by rw [← drop_fun_split_fun f g, H, ← last_fun_split_fun f g, H]; simp

theorem append_fun_inj {α α' : typevec n} {β β' : Type*} {f f' : α ⟹ α'} {g g' : β → β'} :
  f ::: g = f' ::: g' →  f = f' ∧ g = g' :=
split_fun_inj

theorem split_fun_comp {α₀ α₁ α₂ : typevec (n+1)}
    (f₀ : drop α₀ ⟹ drop α₁) (f₁ : drop α₁ ⟹ drop α₂)
    (g₀ : last α₀ → last α₁) (g₁ : last α₁ → last α₂) :
  split_fun (f₁ ⊚ f₀) (g₁ ∘ g₀) = split_fun f₁ g₁ ⊚ split_fun f₀ g₀ :=
eq_of_drop_last_eq (λ _, rfl) rfl

theorem append_fun_comp_split_fun
  {α γ : typevec n} {β δ : Type*} {ε : typevec (n + 1)}
    (f₀ : drop ε ⟹ α) (f₁ : α ⟹ γ)
    (g₀ : last ε → β) (g₁ : β → δ) :
  append_fun f₁ g₁ ⊚ split_fun f₀ g₀ = split_fun (f₁ ⊚ f₀) (g₁ ∘ g₀) :=
(split_fun_comp _ _ _ _).symm

lemma append_fun_comp {α₀ α₁ α₂ : typevec n} {β₀ β₁ β₂ : Type*}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
  f₁ ⊚ f₀ ::: g₁ ∘ g₀ = (f₁ ::: g₁) ⊚ (f₀ ::: g₀) :=
eq_of_drop_last_eq (λ _, rfl) rfl

lemma append_fun_comp' {α₀ α₁ α₂ : typevec n} {β₀ β₁ β₂ : Type*}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
  (f₁ ::: g₁) ⊚ (f₀ ::: g₀) = f₁ ⊚ f₀ ::: g₁ ∘ g₀ :=
eq_of_drop_last_eq (λ _, rfl) rfl

lemma nil_fun_comp {α₀ : typevec 0} (f₀ : α₀ ⟹ fin'.elim0) : nil_fun ⊚ f₀ = f₀ :=
funext $ λ x, fin'.elim0 x

theorem append_fun_comp_id {α : typevec n} {β₀ β₁ β₂ : Type*}
    (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
  @id _ α ::: g₁ ∘ g₀ = (id ::: g₁) ⊚ (id ::: g₀) :=
eq_of_drop_last_eq (λ _, rfl) rfl

@[simp]
theorem drop_fun_comp {α₀ α₁ α₂ : typevec (n+1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
  drop_fun (f₁ ⊚ f₀) = drop_fun f₁ ⊚ drop_fun f₀ := rfl

@[simp]
theorem last_fun_comp {α₀ α₁ α₂ : typevec (n+1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
  last_fun (f₁ ⊚ f₀) = last_fun f₁ ∘ last_fun f₀ := rfl

theorem append_fun_aux {α α' : typevec n} {β β' : Type*}
  (f : α ::: β ⟹ α' ::: β') : drop_fun f ::: last_fun f = f :=
eq_of_drop_last_eq (λ _, rfl) rfl

theorem append_fun_id_id {α : typevec n} {β : Type*} :
  @id n α ::: @_root_.id β = id :=
eq_of_drop_last_eq (λ _, rfl) rfl

instance subsingleton0 : subsingleton (typevec 0) :=
⟨ λ a b, funext $ λ a, fin'.elim0 a  ⟩

run_cmd mk_simp_attr `typevec
-- attribute [typevec]

local prefix `♯`:0 := cast (by try { simp }; congr' 1; try { simp })

def typevec_cases_nil {β : typevec 0 → Sort*} (f : β fin'.elim0) :
  Π v, β v :=
λ v, ♯ f

def typevec_cases_cons (n : ℕ) {β : typevec (n+1) → Sort*} (f : Π t (v : typevec n), β (v ::: t)) :
  Π v, β v :=
λ v, ♯ f v.last v.drop

lemma typevec_cases_nil_append1 {β : typevec 0 → Sort*} (f : β fin'.elim0) :
  typevec_cases_nil f fin'.elim0 = f := rfl

lemma typevec_cases_cons_append1 (n : ℕ) {β : typevec (n+1) → Sort*}
      (f : Π t (v : typevec n), β (v ::: t))
      (v : typevec n) (α) :
  typevec_cases_cons n f (v ::: α) = f α v := rfl

open typevec

def typevec_cases_nil₃ {β : Π v v' : typevec 0, v ⟹ v' → Sort*} (f : β fin'.elim0 fin'.elim0 nil_fun) :
  Π v v' f, β v v' f :=
λ v v' fs,
begin
  refine cast _ f; congr; ext; try { intros; exact fin'.elim0 ‹ fin' 0 ›  }; refl
end

def typevec_cases_cons₃ (n : ℕ) {β : Π v v' : typevec (n+1), v ⟹ v' → Sort*}
  (F : Π t t' (f : t → t') (v v' : typevec n) (fs : v ⟹ v'), β (v ::: t) (v' ::: t') (fs ::: f)) :
  Π v v' fs, β v v' fs :=
begin
  intros v v',
  rw [←append1_drop_last v, ←append1_drop_last v'],
  intro fs,
  rw [←split_drop_fun_last_fun fs],
  apply F
end

def typevec_cases_nil₂ {β : fin'.elim0 ⟹ fin'.elim0 → Sort*}
  (f : β nil_fun) :
  Π f, β f :=
begin
  intro g, have : g = nil_fun, ext ⟨ ⟩,
  rw this, exact f
end

def typevec_cases_cons₂ (n : ℕ) (t t' : Type*) (v v' : typevec (n)) {β : (v ::: t) ⟹ (v' ::: t') → Sort*}
  (F : Π (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) :
  Π fs, β fs :=
begin
  intro fs,
  rw [←split_drop_fun_last_fun fs],
  apply F
end

lemma typevec_cases_nil₂_append_fun {β : fin'.elim0 ⟹ fin'.elim0 → Sort*}
  (f : β nil_fun) :
  typevec_cases_nil₂ f nil_fun = f := rfl

lemma typevec_cases_cons₂_append_fun (n : ℕ) (t t' : Type*) (v v' : typevec (n)) {β : (v ::: t) ⟹ (v' ::: t') → Sort*}
  (F : Π (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) (f fs) :
  typevec_cases_cons₂ n t t' v v' F (fs ::: f) = F f fs := rfl


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

section liftp'
open nat

def repeat : Π (n : ℕ) (t : Sort*), typevec n
| 0 t := fin'.elim0
| (nat.succ i) t := append1 (repeat i t) t


protected def const {β} (x : β) : Π {n} (α : typevec n), α ⟹ repeat _ β
| 0 α i := nil_fun i
| (succ n) α (fin'.raise i) := const (drop α) _
| (succ n) α fin'.last := λ _, x

lemma const_append1 {β γ} (x : γ) {n} (α : typevec n) : typevec.const x (α ::: β) = typevec.const x α ::: (λ _, x) :=
by ext i : 1; cases i; refl

lemma const_nil {β} (x : β) (α : typevec 0) : typevec.const x α = nil_fun :=
by ext i : 1; cases i; refl

def pred_last' (α : typevec n) {β : Type*} (p : β → Prop) : α.append1 β ⟹ repeat _ Prop :=
typevec.const true α ::: p

def curry (F : typevec.{u} (n+1) → Type*) (α : Type u) (β : typevec.{u} n) : Type* :=
F (β ::: α)

def drop_repeat (α : Type*) : Π {n}, drop (repeat (succ n) α) ⟹ repeat n α
| 0 i := fin'.elim0 i
| (succ n) (fin'.raise i) := drop_repeat i
| (succ n) fin'.last := _root_.id

def of_repeat : Π {n i} (x : repeat n Prop i), Prop
| 0 i x := fin'.elim0 i
| (nat.succ n) (fin'.raise i) x := @of_repeat n i x
| (nat.succ n) fin'.last x := x

-- lemma drop_repeat_comp {α : typevec.{u} n.succ} (p : α ⟹ repeat n.succ Prop) (i : fin' n) : (drop_repeat Prop ⊚ drop_fun p) i _ = p _ _ := _

variables  {F : typevec.{u} n → Type*} [mvfunctor F] {α : typevec.{u} n} (p : α ⟹ repeat n Prop)

def subtype_ : Π {n} {α : typevec.{u} n} (p : α ⟹ repeat n Prop), typevec n
| 0 α p := fin'.elim0
| (succ n) α p := @subtype_ n (drop α) (drop_fun p) ::: _root_.subtype (λ x, p fin'.last x)

def subtype_val : Π {n} {α : typevec.{u} n} (p : α ⟹ repeat n Prop), subtype_ p ⟹ α
| 0 α p i := fin'.elim0 i
| (succ n) α p (fin'.raise i) := @subtype_val n _ _ i
| (succ n) α p fin'.last := _root_.subtype.val

lemma subtype_val_append1 {n} {α : typevec.{u} n} (ps : α ⟹ repeat n Prop) {β} (p : β → Prop) : typevec.subtype_val (ps ::: p) = typevec.subtype_val ps ::: subtype.val :=
funext $ by rintro ⟨ ⟩; refl

lemma subtype_val_nil {α : typevec.{u} 0} (ps : α ⟹ repeat 0 Prop) : typevec.subtype_val ps = nil_fun :=
funext $ by rintro ⟨ ⟩; refl

def liftp' : F α → Prop :=
mvfunctor.liftp $ λ i x, of_repeat $ p i x

def append_fun' {α : typevec' n} {β β' : Type*}
  (f : α ⟹ repeat n β') (g : β → β') : append1 α β ⟹ repeat n.succ β' := split_fun f g

lemma liftp_def (x : F α) : liftp' p x ↔ ∃ u : F (subtype_ p), subtype_val p <$$> u = x :=
begin
  dsimp [liftp',mvfunctor.liftp],
  have : (λ (i : fin' n), {x : α i // @of_repeat n i (p i x)}) = (@subtype_ n α p),
  { resetI, clear _inst_1 x F,
    ext i,
    symmetry,
    induction i generalizing p, dsimp [subtype_,append1], rw @i_ih _ (drop_fun p), refl,
    refl },
  congr',
  { ext, rw this, intros, congr; try { assumption },
    ext, refl, intros,
    resetI, clear _inst_1 a_1 a a' x F this,
    symmetry,
    induction a'_1 generalizing a_2 p,
    { dsimp [subtype_val], cases a_3, transitivity, apply a'_1_ih, refl, refl, },
    cases a_3, refl }
end


end liftp'
open nat

section liftp_last_pred_iff
variables  {F : typevec.{u} (n+1) → Type*} [mvfunctor F] {α : typevec.{u} n} (p : α ⟹ repeat n Prop)

open mvfunctor

lemma liftp_last_pred_iff {β} (p : β → Prop) (x : F (α ::: β)) : liftp' (pred_last' _ p) x ↔ liftp (pred_last _ p) x :=
begin
  let f : α ::: β ⟹ repeat _ Prop := (typevec.const true α ::: p : α ::: β ⟹ _),
  have : ∀ (i : fin' (n + 1)), (λ x, of_repeat (pred_last' α p i x)) = (@pred_last _ α _ p _),
  { intros, ext, cases i; dsimp [append1,pred_last',append_fun,split_fun,(∈),set.mem],
    clear_except, dunfold has_add.add nat.add, erw of_repeat,
    induction i_a, dsimp [typevec.const], erw [of_repeat,i_a_ih], refl,
    refl, refl, },
  dsimp [liftp,liftp'],
  congr', ext, rw this,
  intros, ext, congr, simp [this],
  intros, congr', simp [this], ext, refl,
  intros, ext, cases a_3, rw this,
  cases a_3, rw this, rintros _ _ ⟨ ⟩, refl,
end

end liftp_last_pred_iff

end typevec
