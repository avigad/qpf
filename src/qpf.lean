/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

We assume the following:

`P`   : a polynomial functor
`W`   : its W-type
`M`   : its M-type
`F`   : a functor

We define:

`q`   : `qpf` data, representing `F` as a quotient of `P`

The main goal is to construct:

`fix`   : the initial algebra with structure map `F fix → fix`.
`cofix` : the final coalgebra with structure map `cofix → F cofix`

We also show that the composition of qpfs is a qpf, and that the quotient of a qpf
is a qpf.
-/
import tactic.interactive data.multiset M
universe u

/-
Quotients of polynomial functors.

Roughly speaking, saying that `F` is a quotient of a polynomial functor means that for each `α`,
elements of `F α` are represented by pairs `⟨a, f⟩`, where `a` is the shape of the object and
`f` indexes the relevant elements of `α`, in a suitably natural manner.
-/

class qpf (F : Type u → Type u) [functor F] :=
(P         : pfunctor.{u})
(abs       : Π {α}, P.apply α → F α)
(repr      : Π {α}, F α → P.apply α)
(abs_repr  : ∀ {α} (x : F α), abs (repr x) = x)
(abs_map   : ∀ {α β} (f : α → β) (p : P.apply α), abs (f <$> p) = f <$> abs p)

namespace qpf
variables {F : Type u → Type u} [functor F] [q : qpf F]
include q
open functor (liftp liftr)

/-
Show that every qpf is a lawful functor.

Note: every functor has a field, map_comp, and is_lawful_functor has the defining
characterization. We can only propagate the assumption.
-/

theorem id_map {α : Type*} (x : F α) : id <$> x = x :=
by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map], reflexivity }

theorem comp_map {α β γ : Type*} (f : α → β) (g : β → γ) (x : F α) :
  (g ∘ f) <$> x = g <$> f <$> x :=
by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map, ←abs_map, ←abs_map], reflexivity }

theorem is_lawful_functor
    (h : ∀ α β : Type u, @functor.map_const F _ α _ = functor.map ∘ function.const β) :
  is_lawful_functor F :=
{ map_const_eq := h,
  id_map := @id_map F _ _,
  comp_map := @comp_map F _ _ }

/-
Lifting predicates and relations
-/

section
open functor

theorem liftp_iff {α : Type u} (p : α → Prop) (x : F α) :
  liftp p x ↔ ∃ a f, x = abs ⟨a, f⟩ ∧ ∀ i, p (f i) :=
begin
  split,
  { rintros ⟨y, hy⟩, cases h : repr y with a f,
    use [a, λ i, (f i).val], split,
    { rw [←hy, ←abs_repr y, h, ←abs_map], reflexivity },
    intro i, apply (f i).property },
  rintros ⟨a, f, h₀, h₁⟩, dsimp at *,
  use abs (⟨a, λ i, ⟨f i, h₁ i⟩⟩),
  rw [←abs_map, h₀], reflexivity
end

theorem liftp_iff' {α : Type u} (p : α → Prop) (x : F α) :
  liftp p x ↔ ∃ u : q.P.apply α, abs u = x ∧ ∀ i, p (u.snd i) :=
begin
  split,
  { rintros ⟨y, hy⟩, cases h : repr y with a f,
    use ⟨a, λ i, (f i).val⟩, dsimp, split,
    { rw [←hy, ←abs_repr y, h, ←abs_map], reflexivity },
    intro i, apply (f i).property },
  rintros ⟨⟨a, f⟩, h₀, h₁⟩, dsimp at *,
  use abs (⟨a, λ i, ⟨f i, h₁ i⟩⟩),
  rw [←abs_map, ←h₀], reflexivity
end

theorem liftr_iff {α : Type u} (r : α → α → Prop) (x y : F α) :
  liftr r x y ↔ ∃ a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ ∀ i, r (f₀ i) (f₁ i) :=
begin
  split,
  { rintros ⟨u, xeq, yeq⟩, cases h : repr u with a f,
    use [a, λ i, (f i).val.fst, λ i, (f i).val.snd],
    split, { rw [←xeq, ←abs_repr u, h, ←abs_map], refl },
    split, { rw [←yeq, ←abs_repr u, h, ←abs_map], refl },
    intro i, exact (f i).property },
  rintros ⟨a, f₀, f₁, xeq, yeq, h⟩,
  use abs ⟨a, λ i, ⟨(f₀ i, f₁ i), h i⟩⟩,
  dsimp, split,
  { rw [xeq, ←abs_map], refl },
  rw [yeq, ←abs_map], refl
end

end

/-
Think of trees in the `W` type corresponding to `P` as representatives of elements of the
least fixed point of `F`, and assign a canonical representative to each equivalence class
of trees.
-/

/-- does recursion on `q.P.W` using `g : F α → α` rather than `g : P α → α` -/
def recF {α : Type*} (g : F α → α) : q.P.W → α
| ⟨a, f⟩ := g (abs ⟨a, λ x, recF (f x)⟩)

theorem recF_eq {α : Type*} (g : F α → α) (x : q.P.W) :
  recF g x = g (abs (recF g <$> q.P.W_dest x)) :=
by cases x; reflexivity

theorem recF_eq' {α : Type*} (g : F α → α) (a : q.P.A) (f : q.P.B a → q.P.W) :
  recF g ⟨a, f⟩ = g (abs (recF g <$> ⟨a, f⟩)) :=
rfl

/-- two trees are equivalent if their F-abstractions are -/
inductive Wequiv : q.P.W → q.P.W → Prop
| ind (a : q.P.A) (f f' : q.P.B a → q.P.W) :
    (∀ x, Wequiv (f x) (f' x)) → Wequiv ⟨a, f⟩ ⟨a, f'⟩
| abs (a : q.P.A) (f : q.P.B a → q.P.W) (a' : q.P.A) (f' : q.P.B a' → q.P.W) :
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ → Wequiv ⟨a, f⟩ ⟨a', f'⟩
| trans (u v w : q.P.W) : Wequiv u v → Wequiv v w → Wequiv u w

/-- recF is insensitive to the representation -/
theorem recF_eq_of_Wequiv {α : Type u} (u : F α → α) (x y : q.P.W) :
  Wequiv x y → recF u x = recF u y :=
begin
  cases x with a f, cases y with b g,
  intro h, induction h,
  case qpf.Wequiv.ind : a f f' h ih
    { simp only [recF_eq', pfunctor.map_eq, function.comp, ih] },
  case qpf.Wequiv.abs : a f a' f' h ih
    { simp only [recF_eq', abs_map, h] },
  case qpf.Wequiv.trans : x y z e₁ e₂ ih₁ ih₂
    { exact eq.trans ih₁ ih₂ }
end

theorem Wequiv.abs' (x y : q.P.W) (h : abs (q.P.W_dest x) = abs (q.P.W_dest y)) :
  Wequiv x y :=
by { cases x, cases y, apply Wequiv.abs, apply h }

theorem Wequiv.refl (x : q.P.W) : Wequiv x x :=
by cases x with a f; exact Wequiv.abs a f a f rfl

theorem Wequiv.symm (x y : q.P.W) : Wequiv x y → Wequiv y x :=
begin
  cases x with a f, cases y with b g,
  intro h, induction h,
  case qpf.Wequiv.ind : a f f' h ih
    { exact Wequiv.ind _ _ _ ih },
  case qpf.Wequiv.abs : a f a' f' h ih
    { exact Wequiv.abs _ _ _ _ h.symm },
  case qpf.Wequiv.trans : x y z e₁ e₂ ih₁ ih₂
    { exact qpf.Wequiv.trans _ _ _ ih₂ ih₁}
end

/-- maps every element of the W type to a canonical representative -/
def Wrepr : q.P.W → q.P.W := recF (q.P.W_mk ∘ repr)

theorem Wrepr_equiv (x : q.P.W) : Wequiv (Wrepr x) x :=
begin
  induction x with a f ih,
  apply Wequiv.trans,
  { change Wequiv (Wrepr ⟨a, f⟩) (q.P.W_mk (Wrepr <$> ⟨a, f⟩)),
    apply Wequiv.abs',
    have : Wrepr ⟨a, f⟩ = q.P.W_mk (repr (abs (Wrepr <$> ⟨a, f⟩))) := rfl,
    rw [this, pfunctor.W_dest_W_mk, abs_repr],
    reflexivity },
  apply Wequiv.ind, exact ih
end

/-
Define the fixed point as the quotient of trees under the equivalence relation.
-/

def W_setoid : setoid q.P.W :=
⟨Wequiv, @Wequiv.refl _ _ _, @Wequiv.symm _ _ _, @Wequiv.trans _ _ _⟩

local attribute [instance] W_setoid

def fix (F : Type u → Type u) [functor F] [q : qpf F]:= quotient (W_setoid : setoid q.P.W)

def fix.rec {α : Type*} (g : F α → α) : fix F → α :=
quot.lift (recF g) (recF_eq_of_Wequiv g)

def fix_to_W : fix F → q.P.W :=
quotient.lift Wrepr (recF_eq_of_Wequiv (λ x, q.P.W_mk (repr x)))

def fix.mk (x : F (fix F)) : fix F := quot.mk _ (q.P.W_mk (fix_to_W <$> repr x))

def fix.dest : fix F → F (fix F) := fix.rec (functor.map fix.mk)

theorem fix.rec_eq {α : Type*} (g : F α → α) (x : F (fix F)) :
  fix.rec g (fix.mk x) = g (fix.rec g <$> x) :=
have recF g ∘ fix_to_W = fix.rec g,
  by { apply funext, apply quotient.ind, intro x, apply recF_eq_of_Wequiv,
       apply Wrepr_equiv },
begin
  conv { to_lhs, rw [fix.rec, fix.mk], dsimp },
  cases h : repr x with a f,
  rw [pfunctor.map_eq, recF_eq, ←pfunctor.map_eq, pfunctor.W_dest_W_mk, ←pfunctor.comp_map,
      abs_map, ←h, abs_repr, this]
end

theorem fix.ind_aux (a : q.P.A) (f : q.P.B a → q.P.W) :
  fix.mk (abs ⟨a, λ x, ⟦f x⟧⟩) = ⟦⟨a, f⟩⟧ :=
have fix.mk (abs ⟨a, λ x, ⟦f x⟧⟩) = ⟦Wrepr ⟨a, f⟩⟧,
  begin
    apply quot.sound, apply Wequiv.abs',
    rw [pfunctor.W_dest_W_mk, abs_map, abs_repr, ←abs_map, pfunctor.map_eq],
    conv { to_rhs, simp only [Wrepr, recF_eq, pfunctor.W_dest_W_mk, abs_repr] },
    reflexivity
  end,
by { rw this, apply quot.sound, apply Wrepr_equiv }

theorem fix.ind_rec {α : Type*} (g₁ g₂ : fix F → α)
    (h : ∀ x : F (fix F), g₁ <$> x = g₂ <$> x → g₁ (fix.mk x) = g₂ (fix.mk x)) :
  ∀ x, g₁ x = g₂ x :=
begin
  apply quot.ind,
  intro x,
  induction x with a f ih,
  change g₁ ⟦⟨a, f⟩⟧ = g₂ ⟦⟨a, f⟩⟧,
  rw [←fix.ind_aux a f], apply h,
  rw [←abs_map, ←abs_map, pfunctor.map_eq, pfunctor.map_eq],
  dsimp [function.comp],
  congr, ext x, apply ih
end

theorem fix.rec_unique {α : Type*} (g : F α → α) (h : fix F → α)
    (hyp : ∀ x, h (fix.mk x) = g (h <$> x)) :
  fix.rec g = h :=
begin
  ext x,
  apply fix.ind_rec,
  intros x hyp',
  rw [hyp, ←hyp', fix.rec_eq]
end

theorem fix.mk_dest (x : fix F) : fix.mk (fix.dest x) = x :=
begin
  change (fix.mk ∘ fix.dest) x = id x,
  apply fix.ind_rec,
  intro x, dsimp,
  rw [fix.dest, fix.rec_eq, id_map, comp_map],
  intro h, rw h
end

theorem fix.dest_mk (x : F (fix F)) : fix.dest (fix.mk x) = x :=
begin
  unfold fix.dest, rw [fix.rec_eq, ←fix.dest, ←comp_map],
  conv { to_rhs, rw ←(id_map x) },
  congr, ext x, apply fix.mk_dest
end

theorem fix.ind (p : fix F → Prop)
    (h : ∀ x : F (fix F), liftp p x → p (fix.mk x)) :
  ∀ x, p x :=
begin
  apply quot.ind,
  intro x,
  induction x with a f ih,
  change p ⟦⟨a, f⟩⟧,
  rw [←fix.ind_aux a f],
  apply h,
  rw liftp_iff,
  refine ⟨_, _, rfl, _⟩,
  apply ih
end

end qpf

/-
Construct the final coalebra to a qpf.
-/

namespace qpf
variables {F : Type u → Type u} [functor F] [q : qpf F]
include q
open functor (liftp liftr)

/-- does recursion on `q.P.M` using `g : α → F α` rather than `g : α → P α` -/
def corecF {α : Type*} (g : α → F α) : α → q.P.M :=
pfunctor.M_corec (λ x, repr (g x))

theorem corecF_eq {α : Type*} (g : α → F α) (x : α) :
  pfunctor.M_dest (corecF g x) = corecF g <$> repr (g x) :=
by rw [corecF, pfunctor.M_dest_corec]

/- Equivalence -/

/- A pre-congruence on q.P.M *viewed as an F-coalgebra*. Not necessarily symmetric. -/
def is_precongr (r : q.P.M → q.P.M → Prop) : Prop :=
  ∀ ⦃x y⦄, r x y →
    abs (quot.mk r <$> pfunctor.M_dest x) = abs (quot.mk r <$> pfunctor.M_dest y)

/- The maximal congruence on q.P.M -/
def Mcongr : q.P.M → q.P.M → Prop :=
λ x y, ∃ r, is_precongr r ∧ r x y

def cofix (F : Type u → Type u) [functor F] [q : qpf F]:= quot (@Mcongr F _ q)

def cofix.corec {α : Type*} (g : α → F α) : α → cofix F :=
λ x, quot.mk  _ (corecF g x)

def cofix.dest : cofix F → F (cofix F) :=
quot.lift
  (λ x, quot.mk Mcongr <$> (abs (pfunctor.M_dest x)))
  begin
    rintros x y ⟨r, pr, rxy⟩, dsimp,
    have : ∀ x y, r x y → Mcongr x y,
    { intros x y h, exact ⟨r, pr, h⟩ },
    rw [←quot.factor_mk_eq _ _ this], dsimp,
    conv { to_lhs, rw [comp_map, ←abs_map, pr rxy, abs_map, ←comp_map] }
  end

theorem cofix.dest_corec {α : Type u} (g : α → F α) (x : α) :
  cofix.dest (cofix.corec g x) = cofix.corec g <$> g x :=
begin
  conv { to_lhs, rw [cofix.dest, cofix.corec] }, dsimp,
  rw [corecF_eq, abs_map, abs_repr, ←comp_map], reflexivity
end

private theorem cofix.bisim_aux
    (r : cofix F → cofix F → Prop)
    (h' : ∀ x, r x x)
    (h : ∀ x y, r x y → quot.mk r <$> cofix.dest x = quot.mk r <$> cofix.dest y) :
  ∀ x y, r x y → x = y :=
begin
  intro x, apply quot.induction_on x, clear x,
  intros x y, apply quot.induction_on y, clear y,
  intros y rxy,
  apply quot.sound,
  let r' := λ x y, r (quot.mk _ x) (quot.mk _ y),
  have : is_precongr r',
  { intros a b r'ab,
    have  h₀: quot.mk r <$> quot.mk Mcongr <$> abs (pfunctor.M_dest a) =
              quot.mk r <$> quot.mk Mcongr <$> abs (pfunctor.M_dest b) := h _ _ r'ab,
    have h₁ : ∀ u v : q.P.M, Mcongr u v → quot.mk r' u = quot.mk r' v,
    { intros u v cuv, apply quot.sound, dsimp [r'], rw quot.sound cuv, apply h' },
    let f : quot r → quot r' := quot.lift (quot.lift (quot.mk r') h₁)
      begin
        intro c, apply quot.induction_on c, clear c,
        intros c d, apply quot.induction_on d, clear d,
        intros d rcd, apply quot.sound, apply rcd
      end,
    have : f ∘ quot.mk r ∘ quot.mk Mcongr = quot.mk r' := rfl,
    rw [←this, pfunctor.comp_map _ _ f, pfunctor.comp_map _ _ (quot.mk r),
          abs_map, abs_map, abs_map, h₀],
    rw [pfunctor.comp_map _ _ f, pfunctor.comp_map _ _ (quot.mk r),
          abs_map, abs_map, abs_map] },
  refine ⟨r', this, rxy⟩
end

theorem cofix.bisim_rel
    (r : cofix F → cofix F → Prop)
    (h : ∀ x y, r x y → quot.mk r <$> cofix.dest x = quot.mk r <$> cofix.dest y) :
  ∀ x y, r x y → x = y :=
let r' x y := x = y ∨ r x y in
begin
  intros x y rxy,
  apply cofix.bisim_aux r',
  { intro x, left, reflexivity },
  { intros x y r'xy,
    cases r'xy, { rw r'xy },
    have : ∀ x y, r x y → r' x y := λ x y h, or.inr h,
    rw ←quot.factor_mk_eq _ _ this, dsimp,
    rw [@comp_map _ _ q _ _ _ (quot.mk r), @comp_map _ _ q _ _ _ (quot.mk r)],
    rw h _ _ r'xy },
  right, exact rxy
end

theorem cofix.bisim
    (r : cofix F → cofix F → Prop)
    (h : ∀ x y, r x y → liftr r (cofix.dest x) (cofix.dest y)) :
  ∀ x y, r x y → x = y :=
begin
  apply cofix.bisim_rel,
  intros x y rxy,
  rcases (liftr_iff r _ _).mp (h x y rxy) with ⟨a, f₀, f₁, dxeq, dyeq, h'⟩,
  rw [dxeq, dyeq, ←abs_map, ←abs_map, pfunctor.map_eq, pfunctor.map_eq],
  congr' 2, ext i,
  apply quot.sound,
  apply h'
end

theorem cofix.bisim' {α : Type*} (Q : α → Prop) (u v : α → cofix F)
    (h : ∀ x, Q x → ∃ a f f',
      cofix.dest (u x) = abs ⟨a, f⟩ ∧
      cofix.dest (v x) = abs ⟨a, f'⟩ ∧
      ∀ i, ∃ x', Q x' ∧ f i = u x' ∧ f' i = v x') :
  ∀ x, Q x → u x = v x :=
λ x Qx,
let R := λ w z : cofix F, ∃ x', Q x' ∧ w = u x' ∧ z = v x' in
cofix.bisim R
  (λ x y ⟨x', Qx', xeq, yeq⟩,
    begin
      rcases h x' Qx' with ⟨a, f, f', ux'eq, vx'eq, h'⟩,
      rw liftr_iff,
      refine ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩,
    end)
  _ _ ⟨x, Qx, rfl, rfl⟩

end qpf

/-
Composition of qpfs.
-/

namespace qpf

variables {F₂ : Type u → Type u} [functor F₂] [q₂ : qpf F₂]
variables {F₁ : Type u → Type u} [functor F₁] [q₁ : qpf F₁]
include q₂ q₁

def comp : qpf (functor.comp F₂ F₁) :=
{ P := pfunctor.comp (q₂.P) (q₁.P),
  abs := λ α,
    begin
      dsimp [functor.comp],
      intro p,
      exact abs ⟨p.1.1, λ x, abs ⟨p.1.2 x, λ y, p.2 ⟨x, y⟩⟩⟩
    end,
  repr := λ α,
    begin
      dsimp [functor.comp],
      intro y,
      refine ⟨⟨(repr y).1, λ u, (repr ((repr y).2 u)).1⟩, _⟩,
      dsimp [pfunctor.comp],
      intro x,
      exact (repr ((repr y).2 x.1)).snd x.2
    end,
  abs_repr := λ α,
    begin
      abstract {
      dsimp [functor.comp],
      intro x,
      conv { to_rhs, rw ←abs_repr x},
      cases h : repr x with a f,
      dsimp,
      congr,
      ext x,
      cases h' : repr (f x) with b g,
      dsimp, rw [←h', abs_repr] }
    end,
  abs_map := λ α β f,
    begin
      abstract {
      dsimp [functor.comp, pfunctor.comp],
      intro p,
      cases p with a g, dsimp,
      cases a with b h, dsimp,
      symmetry,
      transitivity,
      symmetry,
      apply abs_map,
      congr,
      rw pfunctor.map_eq,
      dsimp [function.comp],
      simp [abs_map],
      split,
      reflexivity,
      ext x,
      rw ←abs_map,
      reflexivity }
    end
}

end qpf

/-
Quotients.

We show that if `F` is a qpf and `G` is a suitable quotient of `F`, then `G` is a qpf.
-/

namespace qpf
variables {F : Type u → Type u} [functor F] [q : qpf F]
variables {G : Type u → Type u} [functor G]
variable  {FG_abs  : Π {α}, F α → G α}
variable  {FG_repr : Π {α}, G α → F α}

def quotient_qpf
    (FG_abs_repr : Π {α} (x : G α), FG_abs (FG_repr x) = x)
    (FG_abs_map  : ∀ {α β} (f : α → β) (x : F α), FG_abs (f <$> x) = f <$> FG_abs x) :
  qpf G :=
{ P        := q.P,
  abs      := λ {α} p, FG_abs (abs p),
  repr     := λ {α} x, repr (FG_repr x),
  abs_repr := λ {α} x, by rw [abs_repr, FG_abs_repr],
  abs_map  := λ {α β} f x, by { rw [abs_map, FG_abs_map] } }

end qpf
