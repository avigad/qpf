/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The initial algebra of a multivariate qpf is again a qpf.
-/
import ..mvpfunctor.W .basic
universes u v

namespace mvqpf

open pfunctor (liftp liftr) category_theory

variables {I J : Type u} {F : fam (I ⊕ J) ⥤ fam J} [q : mvqpf F] {α : fam I} {β : fam J}
include q

/-- does recursion on `q.P.W` using `g : F α → α` rather than `g : P α → α` -/
def recF (g : F.obj (α.append1 β) ⟶ β) : q.P.W α ⟶ β :=
q.P.W_ind (λ j a f' f rec,
  g (abs F _ ⟨a,fam.split_fun f' rec⟩))

theorem recF_eq (g : F.obj (α.append1 β) ⟶ β)
    {i} (a : q.P.A i) (f' : q.P.drop.B i a ⟶ α) (f : q.P.last.B i a ⟶ q.P.W α) :
  recF g (q.P.W_mk a f' f) =  g (abs F _ ⟨a, fam.split_fun f' (f ≫ recF g)⟩) :=
by simp [recF]; rw [mvpfunctor.W_ind_eq]; refl

theorem recF_eq' (g : F.obj (α.append1 β) ⟶ β) :
  recF g = q.P.W_dest' ≫ q.P.map (fam.append_fun (𝟙 _) (recF g)) ≫ abs F _ ≫ g :=
begin
  ext i x : 2,
  apply q.P.W_cases _ _ x,
  intros j a f' f, erw [recF_eq], apply congr_arg (@g _),
  erw [pfunctor.map_eq',mvfunctor.append_fun_comp_split_fun], congr,
  ext : 2, dsimp, rw mvpfunctor.W_path_dest_right_W_path_cases_on, cases f x_2; refl,
end

inductive Wequiv : Π {i}, q.P.W α i → q.P.W α i → Prop
| ind {i} (a : q.P.A i) (f' : q.P.drop.B i a ⟶ α) (f₀ f₁ : q.P.last.B i a ⟶ q.P.W α) :
    (∀ j (x : q.P.last.B i a j), Wequiv ((f₀ : Π j, q.P.last.B i a j → q.P.W α j) x) (f₁ x)) → Wequiv (q.P.W_mk a f' f₀) (q.P.W_mk a f' f₁)
| abs {i} (a₀ : q.P.A i) (f'₀ : q.P.drop.B i a₀ ⟶ α) (f₀ : q.P.last.B i a₀ ⟶ q.P.W α)
          (a₁ : q.P.A i) (f'₁ : q.P.drop.B i a₁ ⟶ α) (f₁ : q.P.last.B i a₁ ⟶ q.P.W α) :
      abs F _ ⟨a₀, q.P.append_contents f'₀ f₀⟩ = abs F _ ⟨a₁, q.P.append_contents f'₁ f₁⟩ →
        Wequiv (q.P.W_mk a₀ f'₀ f₀) (q.P.W_mk a₁ f'₁ f₁)
| trans {i} (u v w : q.P.W α i) : Wequiv u v → Wequiv v w → Wequiv u w

open fam

theorem recF_eq_of_Wequiv (α : fam I) {β : fam J} (u : F.obj (α.append1 β) ⟶ β)
    ⦃i⦄ (x y : q.P.W α i) :
  Wequiv x y → recF u x = recF u y :=
begin
  revert i x, refine q.P.W_cases _ ,
  intros i a₀ f'₀ f₀ y,
  revert i y, refine q.P.W_cases _,
  intros i a₁ f'₁ f₁, introv,
  intro h, induction h,
  case mvqpf.Wequiv.ind : j a f' f₀ f₁ h ih
  { have : f₀ ≫ recF u = f₁ ≫ recF u, { ext : 2, simp [ih] },
    simp only [recF_eq, this, ih, fam.split_fun_comp] },
  case mvqpf.Wequiv.abs : j a₀ f'₀ f₀ a₁ f'₁ f₁ h ih
    { rw [recF_eq'], simp [abs_map_assoc,mvpfunctor.W_dest'_W_mk,h] },
  case mvqpf.Wequiv.trans : i x y z e₁ e₂ ih₁ ih₂
    { exact eq.trans ih₁ ih₂ }
end

theorem Wequiv.abs' ⦃i⦄ (x y : q.P.W α i)
    (h : abs F _ (q.P.W_dest' x) = abs F _ (q.P.W_dest' y)) :
  Wequiv x y :=
begin
  revert i x h, refine q.P.W_cases _,
  intros i a₀ f'₀ f₀ y,
  revert i y, refine q.P.W_cases _,
  intros i a₁ f'₁ f₁, introv,
  apply Wequiv.abs
end

theorem Wequiv.refl ⦃i⦄ (x : q.P.W α i) : Wequiv x x :=
by apply q.P.W_cases _ _ x; intros i a f' f; exact Wequiv.abs a f' f a f' f rfl

theorem Wequiv.symm ⦃i⦄ (x y : q.P.W α i) : Wequiv x y → Wequiv y x :=
begin
  intro h, induction h,
  case mvqpf.Wequiv.ind : i a f' f₀ f₁ h ih
    { exact Wequiv.ind _ _ _ _ ih },
  case mvqpf.Wequiv.abs : i a₀ f'₀ f₀ a₁ f'₁ f₁ h ih
    { exact Wequiv.abs _ _ _ _ _ _ h.symm },
  case mvqpf.Wequiv.trans : i x y z e₁ e₂ ih₁ ih₂
    { exact mvqpf.Wequiv.trans _ _ _ ih₂ ih₁}
end

/-- maps every element of the W type to a canonical representative -/
def Wrepr : q.P.W α ⟶ q.P.W α := recF (repr _ _ ≫ q.P.W_mk')

-- set_option pp.implicit true

theorem Wrepr_W_mk  ⦃i⦄
    (a : q.P.A i) (f' : q.P.drop.B i a ⟶ α) (f : q.P.last.B i a ⟶ q.P.W α) :
  Wrepr (q.P.W_mk a f' f) =
    q.P.W_mk' (repr F _ (abs F _ (q.P.map (fam.append_fun (𝟙 _) Wrepr) ⟨a, q.P.append_contents f' f⟩))) :=
by simp [Wrepr, recF_eq, pfunctor.map_eq,split_fun_comp_right]; refl

theorem Wrepr_W_mk'  ⦃i⦄
    (a : q.P.A i) (f' : q.P.drop.B i a ⟶ α) (f : q.P.last.B i a ⟶ q.P.W α) :
  q.P.W_mk' ≫ Wrepr =
     q.P.map (fam.append_fun (𝟙 _) Wrepr) ≫ abs F _ ≫ repr F (α.append1 _) ≫ q.P.W_mk' :=
by { ext1, ext1 ⟨a,f⟩, simp [mvpfunctor.W_mk',Wrepr_W_mk,abs_map'], congr,
     ext1 ⟨ ⟩; ext1; refl }

theorem Wrepr_equiv ⦃i⦄ (x : q.P.W α i) : Wequiv (Wrepr x) x :=
begin
  apply q.P.W_ind _ _ x, intros i a f' f ih,
  apply Wequiv.trans _ (q.P.W_mk a f' (f ≫ Wrepr)),
  { apply Wequiv.abs',
    rw [Wrepr_W_mk, q.P.W_dest'_W_mk, q.P.W_dest'_W_mk'', abs_repr', pfunctor.map_eq'],
    congr, erw [← split_fun_comp,category.comp_id], },
  apply Wequiv.ind, exact ih
end

theorem Wequiv_map {α β : fam I} (g : α ⟶ β) ⦃i⦄ (x y : q.P.W α i) :
  Wequiv x y → Wequiv (q.P.W_map g x) (q.P.W_map g y) :=
begin
  intro h, induction h,
  case mvqpf.Wequiv.ind : i a f' f₀ f₁ h ih
    { erw [q.P.W_map_W_mk, q.P.W_map_W_mk], apply Wequiv.ind, apply ih },
  case mvqpf.Wequiv.abs : j a₀ f'₀ f₀ a₁ f'₁ f₁ h ih
    { rw [q.P.W_map_W_mk, q.P.W_map_W_mk], apply Wequiv.abs,
      rw [mvpfunctor.append_contents_comp, mvpfunctor.append_contents_comp, ← pfunctor.map_eq', ← pfunctor.map_eq', abs_map', abs_map', h]},
  case mvqpf.Wequiv.trans : i x y z e₁ e₂ ih₁ ih₂
    { apply mvqpf.Wequiv.trans, apply ih₁, apply ih₂ }
end

/-
Define the fixed point as the quotient of trees under the equivalence relation.
-/

def W_setoid (α : fam I) (i) : setoid (q.P.W α i) :=
⟨Wequiv, @Wequiv.refl _ _ _ _ _ _, @Wequiv.symm _ _ _ _ _ _, @Wequiv.trans _ _ _ _ _ _⟩

local attribute [instance] W_setoid

def fix (F : fam (I⊕J) ⥤ fam J) [q : mvqpf F] (α : fam I) : fam J
| i := quotient (W_setoid α i : setoid (q.P.W α i))

def fix.map {α β : fam I} : Π (g : α ⟶ β), fix F α ⟶ fix F β
| g i :=
quotient.lift (λ x : q.P.W α i, ⟦q.P.W_map g x⟧)
  (λ a b h, quot.sound (Wequiv_map _ _ _ h))

section

variable (F)

def pFix : fam I ⥤ fam J :=
{ obj := fix F,
  map := λ X Y f, fix.map f }

end

def Wequiv' : fam.Pred (q.P.W α ⊗ q.P.W α) :=
λ i x, Wequiv x.1 x.2

def pEq : fam.Pred (α ⊗ α) :=
λ i x, x.1 = x.2

def fix.lift (f : q.P.W α ⟶ β) (h : ∀ {i} a b : q.P.W α i, Wequiv a b → f a = f b) : (fix F α ⟶ β) :=
λ i x, quot.lift (@f i) h x

-- TODO: should this be quotient.lift?
def fix.rec (g : F.obj (α.append1 β) ⟶ β) : fix F α ⟶ β :=
fix.lift (recF g) (recF_eq_of_Wequiv α g)

def fix_to_W : fix F α ⟶ q.P.W α :=
fix.lift Wrepr (recF_eq_of_Wequiv α (λ i x, q.P.W_mk' (repr _ _ x)))

def fix.quot.mk : q.P.W α ⟶ fix F α :=
λ i x, quot.mk _ x

@[simp, reassoc]
lemma fix.quot.mk_lift {γ : fam J} (g : q.P.W α ⟶ γ)
      (h : ∀ ⦃i : J⦄ (a b : mvpfunctor.W (P F) α i), Wequiv a b → g a = g b) :
  fix.quot.mk ≫ fix.lift g h = g :=
by ext; simp [fix.lift,fix.quot.mk]

@[simp]
lemma fix.quot.lift_comp {γ : fam J} (f : q.P.W α ⟶ β) (g : β ⟶ γ)
      (h : ∀ ⦃i : J⦄ (a b : mvpfunctor.W (P F) α i), Wequiv a b → f a = f b) :
  fix.lift f h ≫ g = fix.lift (f ≫ g) (λ i a b h', have _, from congr_arg (@g i) (h a b h'), this) :=
by { ext, dsimp [fix.lift,(≫)], induction x_1 using quot.ind, refl }

-- @[extensionality]
-- lemma fix.quot.lift_ext (f g : q.P.W α ⟶ β)
--       (hh : fix_to_W ≫ f = fix_to_W ≫ g)
--       (h h') :
--   fix.lift f @h = fix.lift g @h' := _

def fix.mk : F.obj (α.append1 (fix F α)) ⟶ fix F α :=
repr _ _ ≫ q.P.map (fam.append_fun (𝟙 _) fix_to_W) ≫ q.P.W_mk' ≫ fix.quot.mk

def fix.dest : fix F α ⟶ F.obj (α.append1 (fix F α)) :=
fix.rec (F.map $ fam.append_fun (𝟙 _) fix.mk)

lemma fix_to_W_recF (g : F.obj (α.append1 β) ⟶ β) : fix_to_W ≫ recF g = fix.rec g :=
by { ext i a : 2, apply quotient.induction_on a, intro x,
     apply recF_eq_of_Wequiv, apply Wrepr_equiv }

-- @[extensionality]
lemma fix.quot.lift_ext (f g : fix F α ⟶ β)
      (hh : fix.quot.mk ≫ f = fix.quot.mk ≫ g) :
  f = g :=
begin
  ext a b, apply quot.induction_on b,
  replace hh := λ x, congr_fun (congr_fun hh x),
  intro, apply hh
end

@[reassoc]
theorem fix.rec_eq (g : F.obj (α.append1 β) ⟶ β) : -- ⦃i⦄ (x : F.obj (α.append1 (fix F α)) i) :
  fix.mk ≫ fix.rec g = F.map (fam.append_fun (𝟙 _) (fix.rec g)) ≫ g :=
begin
  conv { to_lhs, rw [fix.rec,fix.mk] }, simp,
  rw [recF_eq', abs_map_assoc, mvpfunctor.W_dest'_W_mk'_assoc, abs_map_assoc, abs_repr_assoc,
        ← category_theory.functor.map_comp_assoc,← append_fun_comp, category.id_comp, fix_to_W_recF],
end

theorem fix.ind_aux {i} (a : q.P.A i) (f' : q.P.drop.B _ a ⟶ α) (f : q.P.last.B i a ⟶ q.P.W α) :
  fix.mk (abs F _ ⟨a, q.P.append_contents f' (λ i x, ⟦f x⟧)⟩) = ⟦q.P.W_mk a f' f⟧ :=
have fix.mk (abs F _ ⟨a, q.P.append_contents f' (λ i x, ⟦f x⟧)⟩) = ⟦Wrepr (q.P.W_mk a f' f)⟧,
  begin
    apply quot.sound, apply Wequiv.abs',
    rw [mvpfunctor.W_dest'_W_mk'', abs_map', abs_repr', ←abs_map', pfunctor.map_eq'],
    conv { to_rhs, rw [Wrepr_W_mk, q.P.W_dest'_W_mk'', abs_repr', pfunctor.map_eq'] },
    congr' 2, rw [mvpfunctor.append_contents, mvpfunctor.append_contents],
    rw [append_fun, append_fun, ←split_fun_comp, ←split_fun_comp],
    reflexivity
  end,
by { rw this, apply quot.sound, apply Wrepr_equiv }

theorem fix.ind_rec {β : fam J} (g₁ g₂ : fix F α ⟶ β)
    (h : ∀ ⦃i⦄ x : unit i ⟶ F.obj (append1 α (fix F α)),
      x ≫ F.map (append_fun (𝟙 _) g₁) = x ≫ F.map (append_fun (𝟙 α) g₂) →
      x ≫ fix.mk ≫ g₁ = x ≫ fix.mk ≫ g₂) :
  g₁ = g₂ :=
begin
  ext i x,
  apply quot.induction_on x, intros x,
  apply q.P.W_ind _ _ x, intros j a f' f ih,
  show g₁ ⟦q.P.W_mk a f' f⟧ = g₂ ⟦q.P.W_mk a f' f⟧,
  rw [←fix.ind_aux a f' f],
  -- specialize h _,
  -- specialize h (value _ ((P F).obj (append1 α (fix F α))) ⟨a,mvpfunctor.append_contents _ f' (λ i x, ⟦f x⟧)⟩ ≫ abs F _) _,
  specialize h (value _ ((P F).obj (append1 α (fix F α))) ⟨a,mvpfunctor.append_contents _ f' (λ i x, ⟦f x⟧)⟩ ≫ abs F _) _,
  -- { replace h := congr_fun (congr_fun h _) (abs F _ ⟨a,mvpfunctor.append_contents _ f' (λ i x, ⟦f x⟧)⟩),
  --   simp at h, exact h },
  -- { ext, cases x_2, },
  { replace h := congr_fun (congr_fun h j) unit.rfl, simp [value] at h, exact h },
  ext _ ⟨⟨⟨ rfl ⟩⟩⟩, simp [value,mvpfunctor.append_contents,append_fun],
  rw [← abs_map',← abs_map',pfunctor.map_eq',pfunctor.map_eq',← split_fun_comp,← split_fun_comp],
  congr' 3, ext, apply ih,
end

theorem fix.rec_unique {β : fam J} (g : F.obj (append1 α β) ⟶ β) (h : fix F α ⟶ β)
    (hyp : fix.mk ≫ h = F.map (append_fun (𝟙 _) h) ≫ g) :
  fix.rec g = h :=
begin
  apply fix.ind_rec,
  intros X x hyp', reassoc hyp',
  rw [hyp, ←hyp', fix.rec_eq]
end

theorem fix.mk_dest : fix.dest ≫ fix.mk = 𝟙 (fix F α) :=
begin
  apply fix.ind_rec,
  rw [fix.dest, fix.rec_eq_assoc, ←category_theory.functor.map_comp_assoc, ←append_fun_comp, category.id_comp, category.comp_id],
  intros X f h, reassoc h,
  rw [h,append_fun_id_id, category_theory.functor.map_id, category.id_comp]
end

theorem fix.dest_mk : fix.mk ≫ fix.dest = 𝟙 (F.obj (append1 α (fix F α))) :=
begin
  unfold fix.dest, rw [fix.rec_eq, ←fix.dest, ←category_theory.functor.map_comp],
  rw [← append_fun_comp, category.id_comp],
  rw [fix.mk_dest, append_fun_id_id, category_theory.functor.map_id]
end

theorem fix.ind {α : fam I} (p : fam.Pred (fix F α))
    (h : ∀ j (x : unit j ⟶ F.obj (α.append1 (fix F α))), liftp (mvfunctor.pred_last α p) x → ∀ a, p j (fix.mk $ x a)) :
  ∀ j x, p j x :=
begin
  intros j a,
  apply quot.induction_on a, clear a,
  intro x,
  apply q.P.W_ind _ _ x, clear x j,
  intros i a f' f ih,
  change p _ ⟦q.P.W_mk a f' f⟧,
  rw [←fix.ind_aux a f' f],
  apply h i (value _ _ (abs F (append1 α (fix F α))
          ⟨a,
           mvpfunctor.append_contents (P F) f' (λ (i_1 : J) (x : (mvpfunctor.last (P F)).B i a i_1), ⟦f x⟧)⟩))
          _ unit.rfl,
  rw [mvqpf.liftp_iff],
  rintros k ⟨⟨rfl⟩⟩,
  refine ⟨a, _, rfl, _⟩,
  rintros (i|i) x, { triv },
  dsimp [mvfunctor.pred_last],
  apply ih
end

instance mvqpf_fix : mvqpf (pFix F) :=
{ P         := q.P.Wp,
  abs       := λ α, fix.quot.mk,
  repr      := λ α, fix_to_W,
  abs_repr  := by { intros α, ext i x, apply quot.induction_on x, intro a, apply quot.sound, apply Wrepr_equiv },
  abs_map   :=
    begin
      intros α β g, conv { to_rhs, dsimp [pFix,functor.map]},
      ext i x, simp [fix.map],
      apply quot.sound, apply Wequiv.refl
    end }

-- def fix.drec {β : fix F α → Type u} (g : Π x : F (α ::: sigma β), β (fix.mk $ (id ::: sigma.fst) <$$> x)) (x : fix F α) : β x :=
-- let y := @fix.rec _ F _ _ α (sigma β) (λ i, ⟨_,g i⟩) x in
-- have x = y.1,
--   by { symmetry, dsimp [y], apply fix.ind_rec _ id _ x, intros x' ih,
--        rw fix.rec_eq, dsimp, simp [append_fun_id_id] at ih,
--        congr, conv { to_rhs, rw [← ih] }, rw [mvfunctor.map_map,← append_fun_comp,id_comp], },
-- cast (by rw this) y.2

end mvqpf
