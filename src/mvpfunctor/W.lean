/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The W construction as a multivariate polynomial functor. 
-/
import .basic
universe u

namespace mvpfunctor
open typevec

variables {n : ℕ} (P : mvpfunctor.{u} (n+1))

def drop : mvpfunctor n :=
{ A := P.A, B := λ a, (P.B a).drop }

def last : pfunctor :=
{ A := P.A, B := λ a, (P.B a).last }

def append_contents {α : typevec n} {β : Type*} 
    {a : P.A} (f' : P.drop.B a ⟹ α) (f : P.last.B a → β) : 
  P.B a ⟹ α.append1 β :=
append_fun f' f ⊚ to_append1_drop_last

def contents_dest_left {α : typevec n} {β : Type*} {a : P.A} (f'f : P.B a ⟹ α.append1 β) : 
  P.drop.B a ⟹ α :=
from_drop_append ⊚ drop_fun f'f 

def contents_dest_right {α : typevec n} {β : Type*} {a : P.A} (f'f : P.B a ⟹ α.append1 β) : 
  P.last.B a → β :=
from_last_append ∘ last_fun f'f

theorem contents_dest_left_append_contents {α : typevec n} {β : Type*} 
    {a : P.A} (f' : P.drop.B a ⟹ α) (f : P.last.B a → β) : 
  P.contents_dest_left (P.append_contents f' f) = f' :=
begin
  rw [contents_dest_left, append_contents, drop_fun_comp, drop_fun_append_fun],
  rw [drop_fun_to_append1_drop_last],
  simp only [typevec.comp, from_drop_append_to_drop_append]
end

theorem contents_dest_right_append_contents {α : typevec n} {β : Type*} 
    {a : P.A} (f' : P.drop.B a ⟹ α) (f : P.last.B a → β) : 
  P.contents_dest_right (P.append_contents f' f) = f :=
begin
  rw [contents_dest_right, append_contents, last_fun_comp, last_fun_append_fun],
  rw [last_fun_to_append1_drop_last],
  simp only [function.comp, from_last_append_to_last_append]
end

theorem append_contents_eta {α : typevec n} {β : Type*} {a : P.A} 
    (f : P.B a ⟹ α.append1 β) : 
  append_contents P (contents_dest_left P f) (contents_dest_right P f) = f :=
by rw [append_contents, contents_dest_left, contents_dest_right, append_fun_aux]

theorem append_fun_comp_append_contents {α γ : typevec n} {β δ : Type*} {a : P.A} 
    (g' : α ⟹ γ) (g : β → δ) (f' : P.drop.B a ⟹ α) (f : P.last.B a → β) : 
  append_fun g' g ⊚ P.append_contents f' f = P.append_contents (g' ⊚ f') (g ∘ f) :=
by rw [append_contents, append_contents, append_fun_comp, comp_assoc]

/- defines a typevec of labels to assign to each node of P.last.W -/
inductive W_path : P.last.W → fin n → Type u 
| root (a : P.A) (f : P.last.B a → P.last.W) (i : fin n) (c : P.drop.B a i) :
    W_path ⟨a, f⟩ i
| child (a : P.A) (f : P.last.B a → P.last.W) (i : fin n) (j : P.last.B a) (c : W_path (f j) i) : 
    W_path ⟨a, f⟩ i

def W_path_cases_on {α : typevec n} {a : P.A} {f : P.last.B a → P.last.W} 
    (g' : P.drop.B a ⟹ α) (g : Π j : P.last.B a, P.W_path (f j) ⟹ α) : 
  P.W_path ⟨a, f⟩ ⟹ α :=
begin
  intros i x, cases x,
  case W_path.root : c { exact g' i c },
  case W_path.child : j c { exact g j i c}
end

def W_path_dest_left {α : typevec n} {a : P.A} {f : P.last.B a → P.last.W} 
    (h : P.W_path ⟨a, f⟩ ⟹ α) :
  P.drop.B a ⟹ α :=
λ i c, h i (W_path.root a f i c)

def W_path_dest_right {α : typevec n} {a : P.A} {f : P.last.B a → P.last.W} 
    (h : P.W_path ⟨a, f⟩ ⟹ α) :
  Π j : P.last.B a, P.W_path (f j) ⟹ α :=
λ j i c, h i (W_path.child a f i j c)

theorem W_path_dest_left_W_path_cases_on 
    {α : typevec n} {a : P.A} {f : P.last.B a → P.last.W} 
    (g' : P.drop.B a ⟹ α) (g : Π j : P.last.B a, P.W_path (f j) ⟹ α) : 
  P.W_path_dest_left (P.W_path_cases_on g' g) = g' := rfl

theorem W_path_dest_right_W_path_cases_on 
    {α : typevec n} {a : P.A} {f : P.last.B a → P.last.W} 
    (g' : P.drop.B a ⟹ α) (g : Π j : P.last.B a, P.W_path (f j) ⟹ α) : 
  P.W_path_dest_right (P.W_path_cases_on g' g) = g := rfl

theorem W_path_cases_on_eta {α : typevec n} {a : P.A} {f : P.last.B a → P.last.W} 
    (h : P.W_path ⟨a, f⟩ ⟹ α) :
  P.W_path_cases_on (P.W_path_dest_left h) (P.W_path_dest_right h) = h :=
by ext i x; cases x; reflexivity

theorem comp_W_path_cases_on {α β : typevec n} (h : α ⟹ β) {a : P.A} {f : P.last.B a → P.last.W} 
    (g' : P.drop.B a ⟹ α) (g : Π j : P.last.B a, P.W_path (f j) ⟹ α) : 
  h ⊚ P.W_path_cases_on g' g = P.W_path_cases_on (h ⊚ g') (λ i, h ⊚ g i) :=
by ext i x; cases x; reflexivity

def Wp : mvpfunctor n :=
{ A := P.last.W, B := P.W_path }

def W (α : typevec n) : Type* := P.Wp.apply α

instance mvfunctor_W : mvfunctor P.W := by delta W; apply_instance

/-
First, describe operations on `W` as a polynomial functor.
-/

def Wp_mk {α : typevec n} (a : P.A) (f : P.last.B a → P.last.W) (f' : P.W_path ⟨a, f⟩ ⟹ α) : 
  P.W α :=
⟨⟨a, f⟩, f'⟩ 

def Wp_rec {α : typevec n} {C : Type*}
  (g : Π (a : P.A) (f : P.last.B a → P.last.W), 
    (P.W_path ⟨a, f⟩ ⟹ α) → (P.last.B a → C) → C) :
  Π (x : P.last.W) (f' : P.W_path x ⟹ α), C
| ⟨a, f⟩ f' := g a f f' (λ i, Wp_rec (f i) (P.W_path_dest_right f' i))

theorem Wp_rec_eq {α : typevec n} {C : Type*}
    (g : Π (a : P.A) (f : P.last.B a → P.last.W), 
      (P.W_path ⟨a, f⟩ ⟹ α) → (P.last.B a → C) → C)
    (a : P.A) (f : P.last.B a → P.last.W) (f' : P.W_path ⟨a, f⟩ ⟹ α) :
  P.Wp_rec g ⟨a, f⟩ f' = g a f f' (λ i, P.Wp_rec g (f i) (P.W_path_dest_right f' i)) :=
rfl

-- Note: we could replace Prop by Type* and obtain a dependent recursor

theorem Wp_ind {α : typevec n} {C : Π x : P.last.W, P.W_path x ⟹ α → Prop}
  (ih : ∀ (a : P.A) (f : P.last.B a → P.last.W) 
    (f' : P.W_path ⟨a, f⟩ ⟹ α), 
      (∀ i : P.last.B a, C (f i) (P.W_path_dest_right f' i)) → C ⟨a, f⟩ f') :
  Π (x : P.last.W) (f' : P.W_path x ⟹ α), C x f'
| ⟨a, f⟩ f' := ih a f f' (λ i, Wp_ind _ _)

/- 
Now think of W as defined inductively by the data ⟨a, f', f⟩ where 
- `a  : P.A` is the shape of the top node
- `f' : P.drop.B a ⟹ α` is the contents of the top node
- `f  : P.last.B a → P.last.W` are the subtrees
 -/

def W_mk {α : typevec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
  P.W α :=
let g  : P.last.B a → P.last.W  := λ i, (f i).fst,
    g' : P.W_path ⟨a, g⟩ ⟹ α := P.W_path_cases_on f' (λ i, (f i).snd) in
⟨⟨a, g⟩, g'⟩

def W_rec {α : typevec n} {C : Type*}
    (g : Π a : P.A, ((P.drop).B a ⟹ α) → ((P.last).B a → P.W α) → ((P.last).B a → C) → C) :
  P.W α → C
| ⟨a, f'⟩ :=
  let g' (a : P.A) (f : P.last.B a → P.last.W) (h : P.W_path ⟨a, f⟩ ⟹ α) 
        (h' : P.last.B a → C) : C := 
      g a (P.W_path_dest_left h) (λ i, ⟨f i, P.W_path_dest_right h i⟩) h' in
  P.Wp_rec g' a f'

theorem W_rec_eq {α : typevec n} {C : Type*} 
    (g : Π a : P.A, ((P.drop).B a ⟹ α) → ((P.last).B a → P.W α) → ((P.last).B a → C) → C)
    (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
  P.W_rec g (P.W_mk a f' f) = g a f' f (λ i, P.W_rec g (f i)) :=
begin
  rw [W_mk, W_rec], dsimp, rw [Wp_rec_eq],
  dsimp only [W_path_dest_left_W_path_cases_on, W_path_dest_right_W_path_cases_on],
  congr; ext1 i; cases (f i); refl
end

theorem W_ind {α : typevec n} {C : P.W α → Prop}
    (ih : ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α), 
      (∀ i, C (f i)) → C (P.W_mk a f' f)) :
  ∀ x, C x :=
begin
  intro x, cases x with a f,
  apply @Wp_ind n P α (λ a f, C ⟨a, f⟩), dsimp,
  intros a f f' ih',
  dsimp [W_mk] at ih, 
  let ih'' := ih a (P.W_path_dest_left f') (λ i, ⟨f i, P.W_path_dest_right f' i⟩),
  dsimp at ih'', rw W_path_cases_on_eta at ih'',
  apply ih'',
  apply ih'
end

theorem W_cases {α : typevec n} {C : P.W α → Prop}
    (ih : ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α), C (P.W_mk a f' f)) :
  ∀ x, C x :=
P.W_ind (λ a f' f ih', ih a f' f)

def W_map {α β : typevec n} (g : α ⟹ β) : P.W α → P.W β :=
λ x, g <$$> x

theorem W_mk_eq {α : typevec n} (a : P.A) (f : P.last.B a → P.last.W) 
    (g' : P.drop.B a ⟹ α) (g : Π j : P.last.B a, P.W_path (f j) ⟹ α) :
  P.W_mk a g' (λ i, ⟨f i, g i⟩) = 
    ⟨⟨a, f⟩, P.W_path_cases_on g' g⟩ := rfl

theorem W_map_W_mk {α β : typevec n} (g : α ⟹ β) 
    (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
  g <$$> P.W_mk a f' f = P.W_mk a (g ⊚ f') (λ i, g <$$> f i) :=
begin
  show _ = P.W_mk a (g ⊚ f') (mvfunctor.map g ∘ f),
  have : mvfunctor.map g ∘ f = λ i, ⟨(f i).fst, g ⊚ ((f i).snd)⟩,
  { ext i, dsimp [function.comp], cases (f i), refl },
  rw this,
  have : f = λ i, ⟨(f i).fst, (f i).snd⟩,
  { ext1, cases (f x), refl },
  rw this, dsimp,
  rw [W_mk_eq, W_mk_eq],
  have h := mvpfunctor.map_eq P.Wp g,
  rw [h, comp_W_path_cases_on]
end

-- TODO: this technical theorem is used in one place below. Can it be avoided?

@[reducible] def apply_append1 {α : typevec n} {β : Type*}
    (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → β) :
  P.apply (append1 α β) :=
⟨a, P.append_contents f' f⟩ 

theorem map_apply_append1 {α γ : typevec n} (g : α ⟹ γ)
  (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
append_fun g (P.W_map g) <$$> P.apply_append1 a f' f = 
  P.apply_append1 a (g ⊚ f') (λ x, P.W_map g (f x)) :=
begin
  rw [apply_append1, apply_append1, append_contents, append_contents, map_eq, append_fun_comp],
  reflexivity
end

/-
Yet another view of the W type: as a fixed point for a multivariate polynomial functor.
These are needed to use the W-construction to construct a fixed point of a qpf, since
the qpf axioms are expressed in terms of `map` on `P`.
-/

def W_mk' {α : typevec n} : P.apply (α.append1 (P.W α)) → P.W α
| ⟨a, f⟩ := P.W_mk a (P.contents_dest_left f) (P.contents_dest_right f)

def W_dest' {α : typevec n} : P.W α → P.apply (α.append1 (P.W α)) :=
P.W_rec (λ a f' f _, ⟨a, P.append_contents f' f⟩)

theorem W_dest'_W_mk {α : typevec n} 
    (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
  P.W_dest' (P.W_mk a f' f) = ⟨a, P.append_contents f' f⟩ :=
by rw [W_dest', W_rec_eq]

theorem W_dest'_W_mk' {α : typevec n} (x : P.apply (α.append1 (P.W α))) :
  P.W_dest' (P.W_mk' x) = x :=
by cases x with a f; rw [W_mk', W_dest'_W_mk, append_contents_eta]

end mvpfunctor

