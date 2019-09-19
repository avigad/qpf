/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The W construction as a multivariate polynomial functor.
-/
import families.mvpfunctor.basic logic.basic
universes u v

namespace mvpfunctor

variables {I J : Type u} (P : mvpfunctor.{u} (J ⊕ I) I)

/- defines a typevec of labels to assign to each node of P.last.W -/
inductive W_path : Π {i}, P.last.W i → J → Type u
| root {i} (a : P.A i) (f : P.last.B i a ⟶ P.last.W) (j : J) (c : P.drop.B i a j) :
    W_path ⟨a, f⟩ j
| child {i} (a : P.A i) (f : P.last.B i a ⟶ P.last.W) (j : I) (x : P.last.B i a j) (k : J) (c : W_path ((f : Π j, P.last.B i a j → P.last.W j) x) k) :
    W_path ⟨a, f⟩ k

variables {α β : fam J} {i : I} {a : P.A i}

def W_path_cases_on {f : P.last.B i a ⟶ P.last.W}
    (g' : P.drop.B i a ⟶ α) (g : Π {j} (x : P.last.B i a j), P.W_path (f x) ⟶ α) :
  P.W_path ⟨a, f⟩ ⟶ α :=
begin
  intros j x, cases x,
  case W_path.root : c { exact g' c },
  case W_path.child : j c { exact g c x_c }
end

def W_path_dest_left {f : P.last.B i a ⟶ P.last.W}
    (h : P.W_path ⟨a, f⟩ ⟶ α) :
  P.drop.B i a ⟶ α :=
λ i c, h (W_path.root a f i c)

def W_path_dest_right {f : P.last.B i a ⟶ P.last.W}
    (h : P.W_path ⟨a, f⟩ ⟶ α) :
  Π j (x : P.last.B i a j), P.W_path (f x) ⟶ α :=
λ j x i c, h (W_path.child _ _ j x _ c)

theorem W_path_dest_left_W_path_cases_on
    {f : P.last.B i a ⟶ P.last.W}
    (g' : P.drop.B i a ⟶ α) (g : Π {j} (x : P.last.B i a j), P.W_path (f x) ⟶ α) :
  P.W_path_dest_left (P.W_path_cases_on g' @g) = g' := rfl

theorem W_path_dest_right_W_path_cases_on
    {f : P.last.B i a ⟶ P.last.W}
    (g' : P.drop.B i a ⟶ α) (g : Π {j} (x : P.last.B i a j), P.W_path (f x) ⟶ α) :
  P.W_path_dest_right (P.W_path_cases_on g' @g) = @g  := rfl

theorem W_path_cases_on_eta {f : P.last.B i a ⟶ P.last.W}
    (h : P.W_path ⟨a, f⟩ ⟶ α) :
  P.W_path_cases_on (P.W_path_dest_left h) (P.W_path_dest_right h) = h :=
by ext i x; cases x; reflexivity

theorem comp_W_path_cases_on (h : α ⟶ β) {a : P.A i} {f : P.last.B i a ⟶ P.last.W}
    (g' : P.drop.B i a ⟶ α) (g : Π j (x : P.last.B i a j), P.W_path (f x) ⟶ α) :
  P.W_path_cases_on g' g ≫ h = P.W_path_cases_on (g' ≫ h) (λ i x, g i x ≫ h) :=
by ext i x; cases x; reflexivity

def Wp : mvpfunctor J I :=
{ A := P.last.W, B := λ _, P.W_path }

def W (α : fam J) : fam I := P.Wp.obj α

-- instance mvfunctor_W : mvfunctor P.W := by delta W; apply_instance

/-
First, describe operations on `W` as a polynomial functor.
-/
def Wp_mk (a : P.A i) (f : P.last.B _ a ⟶ P.last.W) (f' : P.W_path ⟨a, f⟩ ⟶ α) :
  P.W α i :=
⟨⟨a, f⟩, f'⟩

def Wp_ind {C : Π i (x : P.last.W i), (P.W_path x ⟶ α) → Sort*}
  (ih : ∀ i (a : P.A i) (f : P.last.B i a ⟶ P.last.W)
    (f' : P.W_path ⟨a, f⟩ ⟶ α),
      (∀ i (x : P.last.B _ a i), C i (f x) (P.W_path_dest_right f' i _)) → C i ⟨a, f⟩ f') :
  Π i (x : P.last.W i) (f' : P.W_path x ⟶ α), C i x f' :=
by intros; induction x; apply ih; intros; apply x_ih

theorem Wp_ind_eq {C : Π i (x : P.last.W i), (P.W_path x ⟶ α) → Sort*}
    (ih : ∀ i (a : P.A i) (f : P.last.B i a ⟶ P.last.W)
    (f' : P.W_path ⟨a, f⟩ ⟶ α),
      (∀ i (x : P.last.B _ a i), C i (f x) (P.W_path_dest_right f' i _)) → C i ⟨a, f⟩ f')
    {i} (a : P.A i) (f : P.last.B i a ⟶ P.last.W) (f' : P.W_path ⟨a, f⟩ ⟶ α) :
  P.Wp_ind ih _ ⟨a, f⟩ f' = ih i a f f' (λ i x, P.Wp_ind ih i (f x) (P.W_path_dest_right f' i _)) :=
rfl

def Wp_rec {C : Type*}
  (g : Π {i} (a : P.A i) (f : P.last.B i a ⟶ P.last.W),
    (P.W_path ⟨a, f⟩ ⟶ α) → (Π j, P.last.B i a j → C) → C) :
  Π j (x : P.last.W j) (f' : P.W_path x ⟶ α), C
| i x f' := @Wp_ind _ _ P α (λ _ _ _, C) @g i x f'
-- g a f f' (λ (j : I) (x : P.last.B i a j), Wp_rec j (f x) (P.W_path_dest_right f' j x)) .

theorem Wp_rec_eq {C : Type*}
    (g : Π i (a : P.A i) (f : P.last.B i a ⟶  P.last.W),
      (P.W_path ⟨a, f⟩ ⟶ α) → (Π j, P.last.B i a j → C) → C)
    {i} (a : P.A i) (f : P.last.B i a ⟶ P.last.W) (f' : P.W_path ⟨a, f⟩ ⟶ α) :
  P.Wp_rec g _ ⟨a, f⟩ f' = g i a f f' (λ i x, P.Wp_rec g i (f x) (P.W_path_dest_right f' i _)) :=
@Wp_ind_eq _ _ P α (λ _ _ _, C) @g i _ _ f'

-- Note: we could replace Prop by Type* and obtain a dependent recursor

/-
Now think of W as defined inductively by the data ⟨a, f', f⟩ where
- `a  : P.A` is the shape of the top node
- `f' : P.drop.B a ⟹ α` is the contents of the top node
- `f  : P.last.B a → P.last.W` are the subtrees
 -/

def W_mk (a : P.A i) (f' : P.drop.B i a ⟶ α) (f : P.last.B i a ⟶ P.W α) :
  P.W α i :=
let g  : P.last.B i a ⟶ P.last.W  := λ i x, (f x).fst,
    g' : P.W_path ⟨a, g⟩ ⟶ α := P.W_path_cases_on f' (λ i x, (f x).snd) in
⟨⟨a, g⟩, g'⟩

def W_rec {C : Type*}
    (g : Π i (a : P.A i), ((P.drop).B i a ⟶ α) →
             ((P.last).B i a ⟶ P.W α) → (Π j, (P.last).B i a j → C) → C) :
  Π i, P.W α i → C
| i ⟨a, f'⟩ :=
  let g' i (a : P.A i) (f : P.last.B i a ⟶ P.last.W) (h : P.W_path ⟨a, f⟩ ⟶ α)
        (h' : Π j, P.last.B i a j → C) : C :=
      g _ a (P.W_path_dest_left h) (λ i x, ⟨f x, P.W_path_dest_right h i x⟩) h' in
  P.Wp_rec g' i a f'

theorem W_rec_eq {C : Type*}
    (g : Π i (a : P.A i), ((P.drop).B i a ⟶ α) →
              ((P.last).B i a ⟶ P.W α) → (Π j, (P.last).B i a j → C) → C)
    (i) (a : P.A i) (f' : P.drop.B i a ⟶ α) (f : P.last.B i a ⟶ P.W α) :
  P.W_rec g _ (P.W_mk a f' f) = g _ a f' f (λ i x, P.W_rec g i (f x)) :=
begin
  rw [W_mk, W_rec], dsimp, rw [Wp_rec_eq],
  dsimp only [W_path_dest_left_W_path_cases_on, W_path_dest_right_W_path_cases_on],
  congr; ext i x : 2; cases (f x); refl
end

def W_ind {C : Π i, P.W α i → Sort*}
    (ih : ∀ i (a : P.A i) (f' : P.drop.B i a ⟶ α) (f : P.last.B i a ⟶ P.W α),
      (∀ j x, C j $ (f : Π j, P.last.B i a j → P.W α j) x) → C i (P.W_mk a f' f)) :
  ∀ i x, C i x
| i ⟨a,f⟩ :=
@mvpfunctor.Wp_ind _ _ P α (λ i a f, C _ ⟨a, f⟩) (λ i a f f',
  let ih'' := ih _ a (P.W_path_dest_left f') (λ i x, ⟨f x, P.W_path_dest_right f' i x⟩) in
  cast (by dsimp [W_mk]; rw W_path_cases_on_eta) (ih'')) _ _ _

lemma sigma_abs {α} {β : α → Sort*} (a : α) : Π {f g : β a}, psigma.mk a f = psigma.mk a g → f = g
| _ _ rfl := rfl

theorem W_ind_eq {C : Π i, P.W α i → Sort*}
    (g : Π i (a' : P.A i) (f : (P.drop).B i a' ⟶ α)
              (f' : (P.last).B i a' ⟶ P.W α),
              (Π j (a : (P.last).B i a' j),
                C j ((f' : Π j, P.last.B i a' j → P.W α j) a)) → C i (P.W_mk a' f f'))
    (i) (a : P.A i) (f' : P.drop.B i a ⟶ α) (f : P.last.B i a ⟶ P.W α) :
  P.W_ind g _ (P.W_mk a f' f) = g _ a f' f (λ i x, P.W_ind g i (f x)) :=
begin
  apply sigma_abs, dsimp [W_mk],
  conv { to_lhs, rw [W_ind], }, dsimp, congr,
  conv { to_lhs, rw [Wp_ind_eq,cast_eq], },
  congr' 1,
  { ext : 2, rw W_path_dest_right_W_path_cases_on, ext, refl, intro, refl },
  { ext : 1, refl, introv h, cases h, ext, refl, introv h, cases h, rw [W_path_dest_right_W_path_cases_on],
    cases h : f a_2, refl, },
end

theorem W_cases {C : Π i, P.W α i → Prop}
    (ih : ∀ i (a : P.A i) (f' : P.drop.B i a ⟶ α)
              (f : P.last.B i a ⟶ P.W α), C _ (P.W_mk a f' f)) :
  ∀ i x, C i x :=
P.W_ind (λ i a f' f ih', ih i a f' f)

def W_map {α β : fam J} (g : α ⟶ β) : P.W α ⟶ P.W β :=
λ i x, P.Wp.map g x

theorem W_mk_eq {i} (a : P.A i) (f : P.last.B i a ⟶ P.last.W)
    (g' : P.drop.B i a ⟶ α) (g : Π j (x : P.last.B i a j), P.W_path (f x) ⟶ α) :
  P.W_mk a g' (λ i x, ⟨f x, g _ _⟩) =
    ⟨⟨a, f⟩, P.W_path_cases_on g' g⟩ := rfl

theorem W_map_W_mk (g : α ⟶ β)
    {i} (a : P.A i) (f' : P.drop.B i a ⟶ α) (f : P.last.B i a ⟶ P.W α) :
  P.Wp.map g (P.W_mk a f' f) = P.W_mk a (f' ≫ g) (f ≫ P.Wp.map g) :=
begin
  have : f ≫ P.Wp.map g = λ _ i, ⟨(f i).fst, ((f i).snd) ≫ g⟩,
  { ext i x : 2, dsimp [function.comp,(≫)], cases (f x), refl },
  simp [this,W_mk,W_mk_eq,pfunctor.map_eq P.Wp g,comp_W_path_cases_on],
end

-- TODO: this technical theorem is used in one place in constructing the initial algebra.
-- Can it be avoided?

@[reducible] def apply_append1 {β : fam I}
    {i} (a : P.A i) (f' : P.drop.B i a ⟶ α) (f : P.last.B i a ⟶ β) :
  P.obj (α.append1 β) i :=
⟨a, fam.split_fun f' f ⟩

theorem map_apply_append1 {γ : fam J} (g : α ⟶ γ)
  {i} (a : P.A i) (f' : P.drop.B i a ⟶ α) (f : P.last.B i a ⟶ P.W α) :
P.map (fam.append_fun g (P.W_map g)) (P.apply_append1 a f' f) =
  P.apply_append1 a (f' ≫ g) (f ≫ P.W_map g) :=
by erw [apply_append1, apply_append1, pfunctor.map_eq, ← fam.split_fun_comp]

/-
Yet another view of the W type: as a fixed point for a multivariate polynomial functor.
These are needed to use the W-construction to construct a fixed point of a qpf, since
the qpf axioms are expressed in terms of `map` on `P`.
-/
def W_mk' : P.obj (α.append1 (P.W α)) ⟶ P.W α :=
show Π i, P.obj (α.append1 (P.W α)) i → P.W α i, from
λ (i : I) ⟨a, f⟩, P.W_mk a (fam.drop_fun f) (fam.last_fun f)

def W_dest' : P.W α ⟶ P.obj (α.append1 (P.W α)) :=
show Π i, P.W α i → P.obj (α.append1 (P.W α)) i, from
P.W_ind (λ j a f f' _,
  show pfunctor.obj P (fam.append1 α (W P α)) j,
  from ⟨a,fam.split_fun f f'⟩)

theorem W_dest'_W_mk {i}
    (a : P.A i) (f' : P.drop.B i a ⟶ α) (f : P.last.B i a ⟶ P.W α) :
  P.W_dest' (P.W_mk a f' f) = ⟨a, fam.split_fun f' f⟩ :=
by simp [W_dest']; erw [W_ind_eq]

theorem W_dest'_W_mk' {i} (x : P.obj (α.append1 (P.W α)) i) :
  P.W_dest' (P.W_mk' x) = x :=
by cases x with a f; simp! [W_mk']; rw [W_dest'_W_mk, fam.split_drop_fun_last_fun]

end mvpfunctor
