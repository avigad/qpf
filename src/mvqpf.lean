/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Multivariate versions of qpf's.
-/
import .mvpfunctor
universe u

/-
Multivariate W as a polynomial functor.
-/

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

def W_mvpfunctor : mvpfunctor n :=
{ A := P.last.W, B := P.W_path }

def W (α : typevec n) : Type* := P.W_mvpfunctor.apply α

instance mvfunctor_W : mvfunctor P.W := by delta W; apply_instance

def W_rec' {α : typevec n} {C : Type*}
  (g : Π (a : P.A) (f : P.last.B a → P.last.W), 
    (P.W_path ⟨a, f⟩ ⟹ α) → (P.last.B a → C) → C) :
  Π (x : P.last.W) (f' : P.W_path x ⟹ α), C
| ⟨a, f⟩ f' := g a f f' (λ i, W_rec' (f i) (P.W_path_dest_right f' i))

theorem W_rec_eq' {α : typevec n} {C : Type*}
    (g : Π (a : P.A) (f : P.last.B a → P.last.W), 
      (P.W_path ⟨a, f⟩ ⟹ α) → (P.last.B a → C) → C)
    (a : P.A) (f : P.last.B a → P.last.W) (f' : P.W_path ⟨a, f⟩ ⟹ α) :
  P.W_rec' g ⟨a, f⟩ f' = g a f f' (λ i, P.W_rec' g (f i) (P.W_path_dest_right f' i)) :=
rfl


-- Note: we could replace Prop by Type* and obtain a dependent recursor

theorem W_ind' {α : typevec n} {C : Π x : P.last.W, P.W_path x ⟹ α → Prop}
  (ih : ∀ (a : P.A) (f : P.last.B a → P.last.W) 
    (f' : P.W_path ⟨a, f⟩ ⟹ α), 
      (∀ i : P.last.B a, C (f i) (P.W_path_dest_right f' i)) → C ⟨a, f⟩ f') :
  Π (x : P.last.W) (f' : P.W_path x ⟹ α), C x f'
| ⟨a, f⟩ f' := ih a f f' (λ i, W_ind' _ _)

/- express principles in more convenient form -/

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
  P.W_rec' g' a f'

theorem W_rec_eq {α : typevec n} {C : Type*} 
    (g : Π a : P.A, ((P.drop).B a ⟹ α) → ((P.last).B a → P.W α) → ((P.last).B a → C) → C)
    (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
  P.W_rec g (P.W_mk a f' f) = g a f' f (λ i, P.W_rec g (f i)) :=
begin
  rw [W_mk, W_rec], dsimp, rw [W_rec_eq'],
  dsimp only [W_path_dest_left_W_path_cases_on, W_path_dest_right_W_path_cases_on],
  congr; ext1 i; cases (f i); refl
end

theorem W_ind {α : typevec n} {C : P.W α → Prop}
    (ih : ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α), 
      (∀ i, C (f i)) → C (P.W_mk a f' f)) :
  ∀ x, C x :=
begin
  intro x, cases x with a f,
  apply @W_ind' n P α (λ a f, C ⟨a, f⟩), dsimp,
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

def W_dest {α : typevec n} : P.W α → P.apply (α.append1 (P.W α)) :=
P.W_rec (λ a f' f _, ⟨a, P.append_contents f' f⟩)

theorem W_dest_W_mk {α : typevec n} 
    (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
  P.W_dest (P.W_mk a f' f) = ⟨a, P.append_contents f' f⟩ :=
by rw [W_dest, W_rec_eq]

def W_mk' {α : typevec n} : P.apply (α.append1 (P.W α)) → P.W α
| ⟨a, f⟩ := P.W_mk a (P.contents_dest_left f) (P.contents_dest_right f)

theorem W_dest_W_mk' {α : typevec n} (x : P.apply (α.append1 (P.W α))) :
  P.W_dest (P.W_mk' x) = x :=
by cases x with a f; rw [W_mk', W_dest_W_mk, append_contents_eta]

def W_map {α β : typevec n} (g : α ⟹ β) : P.W α → P.W β :=
λ x, g <$$> x

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

/- TODO: shameless hackery here. Clean this up. -/

def W_shape : P.last.W → P.A
| ⟨a, f⟩ := a

def W_dest'' {α : typevec n} : Π (a : P.last.W) (f' : P.W_path a ⟹ α),
  (P.drop.B (P.W_shape a) ⟹ α) × (P.last.B (P.W_shape a) → P.W α)
| ⟨a, f⟩ f' := (P.W_path_dest_left f', λ i, ⟨f i, P.W_path_dest_right f' i⟩)

theorem W_map_W_mk_aux {α β : typevec n} (a : P.last.W) (f' : P.W_path a ⟹ α) 
    (g : α ⟹ β) :
  P.W_mk (P.W_shape a) (g ⊚ (P.W_dest'' a f').fst) 
      (mvfunctor.map g ∘ (P.W_dest'' a f').snd) = ⟨a, g ⊚ f'⟩ :=
begin
  induction a with a f ih,
  dsimp [W_shape, W_dest''] at *,
  rw [W_mk], dsimp,
  congr, 
  transitivity
    W_path_cases_on P (g ⊚ W_path_dest_left P f')
      (λ (i : (last P).B a), g ⊚ (W_path_dest_right P f' i)),
  { reflexivity },
  rw [←comp_W_path_cases_on],
  congr,
  apply W_path_cases_on_eta
end

theorem W_map_W_mk {α β : typevec n} (g : α ⟹ β) 
    (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
  g <$$> P.W_mk a f' f = P.W_mk a (g ⊚ f') (λ i, g <$$> f i) :=
begin
  conv { to_lhs, rw [W_mk], dsimp},
  have h := mvpfunctor.map_eq P.W_mvpfunctor g,
  rw h, 
  rw ←W_map_W_mk_aux, dsimp [W_shape, W_dest''],
  rw [W_path_dest_left_W_path_cases_on, W_path_dest_right_W_path_cases_on],
  congr; ext1 i,
  cases (f i), refl
end

end mvpfunctor

/-
Multivariate qpfs.
-/

class mvqpf {n : ℕ} (F : typevec.{u} n → Type*) [mvfunctor F] :=
(P         : mvpfunctor.{u} n)
(abs       : Π {α}, P.apply α → F α)
(repr'     : Π {α}, F α → P.apply α)
(abs_repr' : ∀ {α} (x : F α), abs (repr' x) = x)
(abs_map   : ∀ {α β} (f : α ⟹ β) (p : P.apply α), abs (f <$$> p) = f <$$> abs p)

namespace mvqpf
variables {n : ℕ} {F : typevec.{u} n → Type*} [mvfunctor F] [q : mvqpf F]
include q

def repr {α : typevec n} (x : F α) := repr' n x

theorem abs_repr {α : typevec n} (x : F α) : abs (repr x) = x :=
abs_repr' n x

attribute [simp] abs_repr

/- 
Show that every mvqpf is a lawful mvfunctor. 
-/

theorem id_map {α : typevec n} (x : F α) : typevec.id <$$> x = x :=
by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map], reflexivity }

theorem comp_map {α β γ : typevec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α) : 
  (g ⊚ f) <$$> x = g <$$> f <$$> x :=
by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map, ←abs_map, ←abs_map], reflexivity }

instance is_lawful_mvfunctor : is_lawful_mvfunctor F :=
{ mv_id_map := @id_map n F _ _,
  mv_comp_map := @comp_map n F _ _ }

end mvqpf

/-
Consruct fix.
-/

namespace mvqpf
open typevec

variables {n : ℕ} {F : typevec.{u} (n+1) → Type u} [mvfunctor F] [q : mvqpf F]
include q

/-- does recursion on `q.P.W` using `g : F α → α` rather than `g : P α → α` -/
def recF {α : typevec n} {β : Type*} (g : F (α.append1 β) → β) : q.P.W α → β :=
q.P.W_rec (λ a f' f rec, g (abs ⟨a, mvpfunctor.append_contents _ f' rec⟩)) 

theorem recF_eq {α : typevec n} {β : Type*} (g : F (α.append1 β) → β) 
    (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f : q.P.last.B a → q.P.W α) :
  recF g (q.P.W_mk a f' f) =  g (abs ⟨a, mvpfunctor.append_contents _ f' (recF g ∘ f)⟩) :=
by rw [recF, mvpfunctor.W_rec_eq]

theorem recF_eq' {α : typevec n} {β : Type*} (g : F (α.append1 β) → β) 
    (x : q.P.W α) :
  recF g x = g (abs ((append_fun id (recF g)) <$$> q.P.W_dest x)) :=
begin
  apply q.P.W_cases _ x,
  intros a f' f,
  rw [recF_eq, q.P.W_dest_W_mk, mvpfunctor.map_eq, mvpfunctor.append_fun_comp_append_contents,
    typevec.id_comp]
end

inductive Wequiv {α : typevec n} : q.P.W α → q.P.W α → Prop 
| ind (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f₀ f₁ : q.P.last.B a → q.P.W α) :
    (∀ x, Wequiv (f₀ x) (f₁ x)) → Wequiv (q.P.W_mk a f' f₀) (q.P.W_mk a f' f₁)
| abs (a₀ : q.P.A) (f'₀ : q.P.drop.B a₀ ⟹ α) (f₀ : q.P.last.B a₀ → q.P.W α) 
      (a₁ : q.P.A) (f'₁ : q.P.drop.B a₁ ⟹ α) (f₁ : q.P.last.B a₁ → q.P.W α) :
      abs ⟨a₀, q.P.append_contents f'₀ f₀⟩ = abs ⟨a₁, q.P.append_contents f'₁ f₁⟩ → 
        Wequiv (q.P.W_mk a₀ f'₀ f₀) (q.P.W_mk a₁ f'₁ f₁)
| trans (u v w : q.P.W α) : Wequiv u v → Wequiv v w → Wequiv u w

theorem recF_eq_of_Wequiv (α : typevec n) {β : Type*} (u : F (α.append1 β) → β) 
    (x y : q.P.W α) :
  Wequiv x y → recF u x = recF u y :=
begin
  apply q.P.W_cases _ x,
  intros a₀ f'₀ f₀,
  apply q.P.W_cases _ y,
  intros a₁ f'₁ f₁,
  intro h, induction h,
  case mvqpf.Wequiv.ind : a f' f₀ f₁ h ih { simp only [recF_eq, function.comp, ih] },
  case mvqpf.Wequiv.abs : a₀ f'₀ f₀ a₁ f'₁ f₁ h ih 
    { simp only [recF_eq', abs_map, mvpfunctor.W_dest_W_mk, h] },  
  case mvqpf.Wequiv.trans : x y z e₁ e₂ ih₁ ih₂
    { exact eq.trans ih₁ ih₂ } 
end

theorem Wequiv.abs' {α : typevec n} (x y : q.P.W α) 
    (h : abs (q.P.W_dest x) = abs (q.P.W_dest y)) :
  Wequiv x y :=
begin
  revert h,
  apply q.P.W_cases _ x,
  intros a₀ f'₀ f₀,
  apply q.P.W_cases _ y,
  intros a₁ f'₁ f₁,
  apply Wequiv.abs
end

theorem Wequiv.refl {α : typevec n} (x : q.P.W α) : Wequiv x x := 
by apply q.P.W_cases _ x; intros a f' f; exact Wequiv.abs a f' f a f' f rfl

theorem Wequiv.symm {α : typevec n} (x y : q.P.W α) : Wequiv x y → Wequiv y x :=
begin
  intro h, induction h,
  case mvqpf.Wequiv.ind : a f' f₀ f₁ h ih 
    { exact Wequiv.ind _ _ _ _ ih },
  case mvqpf.Wequiv.abs : a₀ f'₀ f₀ a₁ f'₁ f₁ h ih 
    { exact Wequiv.abs _ _ _ _ _ _ h.symm },
  case mvqpf.Wequiv.trans : x y z e₁ e₂ ih₁ ih₂
    { exact mvqpf.Wequiv.trans _ _ _ ih₂ ih₁}
end

/-- maps every element of the W type to a canonical representative -/
def Wrepr {α : typevec n} : q.P.W α → q.P.W α := recF (q.P.W_mk' ∘ repr)

theorem Wrepr_W_mk  {α : typevec n} 
    (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f : q.P.last.B a → q.P.W α) :
  Wrepr (q.P.W_mk a f' f) = 
    q.P.W_mk' (repr (abs ((append_fun id Wrepr) <$$> ⟨a, q.P.append_contents f' f⟩))) :=
by rw [Wrepr, recF_eq', q.P.W_dest_W_mk]

theorem Wrepr_equiv {α : typevec n} (x : q.P.W α) : Wequiv (Wrepr x) x :=
begin
  apply q.P.W_ind _ x, intros a f' f ih,
  apply Wequiv.trans _ (q.P.W_mk' ((append_fun id Wrepr) <$$> ⟨a, q.P.append_contents f' f⟩)),
  { apply Wequiv.abs',
    rw [Wrepr_W_mk, q.P.W_dest_W_mk', q.P.W_dest_W_mk', abs_repr] },
  rw [q.P.map_eq, mvpfunctor.W_mk', q.P.append_fun_comp_append_contents, id_comp,
      q.P.contents_dest_left_append_contents, q.P.contents_dest_right_append_contents],
  apply Wequiv.ind, exact ih
end

theorem Wequiv_map {α β : typevec n} (g : α ⟹ β) (x y : q.P.W α) : 
  Wequiv x y → Wequiv (g <$$> x) (g <$$> y) :=
begin
  intro h, induction h,
  case mvqpf.Wequiv.ind : a f' f₀ f₁ h ih 
    { rw [q.P.W_map_W_mk, q.P.W_map_W_mk], apply Wequiv.ind, apply ih },
  case mvqpf.Wequiv.abs : a₀ f'₀ f₀ a₁ f'₁ f₁ h ih 
    { rw [q.P.W_map_W_mk, q.P.W_map_W_mk], apply Wequiv.abs,
      show abs (q.P.apply_append1 a₀ (g ⊚ f'₀) (λ x, q.P.W_map g (f₀ x))) = 
           abs (q.P.apply_append1 a₁ (g ⊚ f'₁) (λ x, q.P.W_map g (f₁ x))),
      rw [←q.P.map_apply_append1, ←q.P.map_apply_append1, abs_map, abs_map, h]},
  case mvqpf.Wequiv.trans : x y z e₁ e₂ ih₁ ih₂
    { apply mvqpf.Wequiv.trans, apply ih₁, apply ih₂ }
end

/-
Define the fixed point as the quotient of trees under the equivalence relation.
-/

def W_setoid (α : typevec n) : setoid (q.P.W α) :=
⟨Wequiv, @Wequiv.refl _ _ _ _ _, @Wequiv.symm _ _ _ _ _, @Wequiv.trans _ _ _ _ _⟩ 

local attribute [instance] W_setoid

def fix {n : ℕ} (F : typevec (n+1) → Type*) [mvfunctor F] [q : mvqpf F] (α : typevec n) := 
quotient (W_setoid α : setoid (q.P.W α))

def fix.map {α β : typevec n} (g : α ⟹ β) : fix F α → fix F β :=
quotient.lift (λ x : q.P.W α, ⟦q.P.W_map g x⟧) 
  (λ a b h, quot.sound (Wequiv_map _ _ _ h))

instance : mvfunctor (fix F) :=
{ map := @fix.map _ _ _ _}

variable {α : typevec.{u} n} 

-- TODO: should this be quotient.lift?
def fix.rec {β : Type u} (g : F (append1 α β) → β) : fix F α → β :=
quot.lift (recF g) (recF_eq_of_Wequiv α g)

def fix_to_W : fix F α → q.P.W α := 
quotient.lift Wrepr (recF_eq_of_Wequiv α (λ x, q.P.W_mk' (repr x)))

def fix.mk (x : F (append1 α (fix F α))) : fix F α := 
  quot.mk _ (q.P.W_mk' (append_fun id fix_to_W <$$> repr x))

def fix.dest : fix F α → F (append1 α (fix F α)) :=
fix.rec (mvfunctor.map (append_fun id fix.mk))

theorem fix.rec_eq {β : Type u} (g : F (append1 α β) → β) (x : F (append1 α (fix F α))) :
  fix.rec g (fix.mk x) = g (append_fun id (fix.rec g) <$$> x) :=
have recF g ∘ fix_to_W = fix.rec g, 
  by { apply funext, apply quotient.ind, intro x, apply recF_eq_of_Wequiv, 
       apply Wrepr_equiv },
begin
  conv { to_lhs, rw [fix.rec, fix.mk], dsimp },
  cases h : repr x with a f,
  rw [mvpfunctor.map_eq, recF_eq', ←mvpfunctor.map_eq, mvpfunctor.W_dest_W_mk'],
  rw [←mvpfunctor.comp_map, abs_map, ←h, abs_repr, ←append_fun_comp, id_comp, this]
end

theorem fix.ind_aux (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f : q.P.last.B a → q.P.W α) :
  fix.mk (abs ⟨a, q.P.append_contents f' (λ x, ⟦f x⟧)⟩) = ⟦q.P.W_mk a f' f⟧ :=
have fix.mk (abs ⟨a, q.P.append_contents f' (λ x, ⟦f x⟧)⟩) = ⟦Wrepr (q.P.W_mk a f' f)⟧,
  begin
    apply quot.sound, apply Wequiv.abs',
    rw [mvpfunctor.W_dest_W_mk', abs_map, abs_repr, ←abs_map, mvpfunctor.map_eq],
    conv { to_rhs, rw [Wrepr_W_mk, q.P.W_dest_W_mk', abs_repr, mvpfunctor.map_eq] },
    congr' 2, rw [mvpfunctor.append_contents, mvpfunctor.append_contents],
    rw [←typevec.comp_assoc, ←append_fun_comp, ←typevec.comp_assoc, ←append_fun_comp],
    reflexivity
  end,
by { rw this, apply quot.sound, apply Wrepr_equiv }

theorem fix.ind {β : Type*} (g₁ g₂ : fix F α → β) 
    (h : ∀ x : F (append1 α (fix F α)), 
      (append_fun id g₁) <$$> x = (append_fun id g₂) <$$> x → g₁ (fix.mk x) = g₂ (fix.mk x)) :
  ∀ x, g₁ x = g₂ x :=
begin
  apply quot.ind,
  intro x,
  apply q.P.W_ind _ x, intros a f' f ih,
  show g₁ ⟦q.P.W_mk a f' f⟧ = g₂ ⟦q.P.W_mk a f' f⟧,
  rw [←fix.ind_aux a f' f], apply h,
  rw [←abs_map, ←abs_map, mvpfunctor.map_eq, mvpfunctor.map_eq],
  congr' 2, rw [mvpfunctor.append_contents, ←comp_assoc, ←comp_assoc], 
  rw [←append_fun_comp, ←append_fun_comp],
  have : g₁ ∘ (λ x, ⟦f x⟧) = g₂ ∘ (λ x, ⟦f x⟧),
  { ext x, exact ih x },
  rw this 
end

theorem fix.rec_unique {β : Type*} (g : F (append1 α β) → β) (h : fix F α → β)
    (hyp : ∀ x, h (fix.mk x) = g (append_fun id h <$$> x)) :
  fix.rec g = h :=
begin
  ext x,
  apply fix.ind,
  intros x hyp',
  rw [hyp, ←hyp', fix.rec_eq]
end

theorem fix.mk_dest (x : fix F α) : fix.mk (fix.dest x) = x :=
begin
  change (fix.mk ∘ fix.dest) x = x,
  apply fix.ind,
  intro x, dsimp,
  rw [fix.dest, fix.rec_eq, ←comp_map, ←append_fun_comp, id_comp],
  intro h, rw h, 
  show fix.mk (append_fun id id <$$> x) = fix.mk x,
  rw [append_fun_id_id, id_map]
end

theorem fix.dest_mk (x : F (append1 α (fix F α))) : fix.dest (fix.mk x) = x :=
begin
  unfold fix.dest, rw [fix.rec_eq, ←fix.dest, ←comp_map],
  conv { to_rhs, rw ←(id_map x) },
  rw [←append_fun_comp, id_comp],
  have : fix.mk ∘ fix.dest = id, {ext x, apply fix.mk_dest },
  rw [this, append_fun_id_id]
end

instance mvqpf_fix (α : typevec n) : mvqpf (fix F) :=
{
  P         := q.P.W_mvpfunctor,
  abs       := λ α, quot.mk Wequiv,
  repr'     := λ α, fix_to_W,
  abs_repr' := by { intros α, apply quot.ind, intro a, apply quot.sound, apply Wrepr_equiv },
  abs_map   := 
    begin 
      intros α β g x, conv { to_rhs, dsimp [mvfunctor.map]},
      rw fix.map, apply quot.sound,
      apply Wequiv.refl
    end
}

end mvqpf
