/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import data.pfun category.functor category.applicative

universes u v

lemma eq_mp_heq :
  ∀ {α β : Sort*} {a : α} {a' : β} (h₂ : a == a'), (eq.mp (type_eq_of_heq h₂) a) = a'
| α ._ a a' heq.rfl := rfl

namespace sigma
variables {α₁ α₂ α₃ : Type u}
variables {β₁ : α₁ → Type v} {β₂ : α₂ → Type v} {β₃ : α₃ → Type v}
variables {g : sigma β₂ → sigma β₃} {f : sigma β₁ → sigma β₂}

theorem eq_fst {s₁ s₂ : sigma β₁} : s₁ = s₂ → s₁.1 = s₂.1 :=
by cases s₁; cases s₂; cc

theorem eq_snd {s₁ s₂ : sigma β₁} : s₁ = s₂ → s₁.2 == s₂.2 :=
by cases s₁; cases s₂; cc

@[extensionality]
lemma ext {x₀ x₁ : sigma β₁}
  (h₀ : x₀.1 = x₁.1)
  (h₁ : x₀.1 = x₁.1 → x₀.2 == x₁.2) :
  x₀ = x₁ :=
by casesm* sigma _; cases h₀; cases h₁ h₀; refl

lemma eta (x : sigma β₁) : sigma.mk x.1 x.2 = x :=
by cases x; refl

end sigma

namespace roption
variables {α : Type*} {β : Type*} {γ : Type*}

open function
lemma assert_if_neg {p : Prop}
  (x : p → roption α)
  (h : ¬ p)
: assert p x = roption.none :=
by { dsimp [assert,roption.none],
     have : (∃ (h : p), (x h).dom) ↔ false,
     { split ; intros h' ; repeat { cases h' with h' },
       exact h h' },
     congr,
     repeat { rw this <|> apply hfunext },
     intros h h', cases h', }

lemma assert_if_pos {p : Prop}
  (x : p → roption α)
  (h : p)
: assert p x = x h :=
by { dsimp [assert],
     have : (∃ (h : p), (x h).dom) ↔ (x h).dom,
     { split ; intros h'
       ; cases h' <|> split
       ; assumption, },
     cases hx : x h, congr, rw [this,hx],
     apply hfunext, rw [this,hx],
     intros, simp [hx] }

@[simp]
lemma roption.none_bind {α β : Type*} (f : α → roption β)
: roption.none >>= f = roption.none :=
by simp [roption.none,has_bind.bind,roption.bind,assert_if_neg]

end roption

namespace monad

@[simp]
lemma bind_pure_star {m} [monad m] [is_lawful_monad m] (x : m punit) :
  x >>= (λ (_x : punit), pure punit.star : punit → m punit) = x :=
by { transitivity,
     { apply congr_arg, ext z, cases z, refl },
     { simp } }

variables {α β γ : Type u}
variables {m : Type u → Type v} [monad m]

@[reducible]
def pipe (a : α → m β) (b : β → m γ) : α → m γ :=
λ x, a x >>= b

infixr ` >=> `:55 := pipe

@[functor_norm]
lemma map_bind_eq_bind_comp {α β γ} {m} [monad m] [is_lawful_monad m]
  (f : α → β) (cmd : m α) (g : β → m γ) :
  (f <$> cmd) >>= g = cmd >>= g ∘ f :=
by rw [← bind_pure_comp_eq_map,bind_assoc,(∘)]; simp

@[functor_norm]
lemma bind_map {α β γ} {m} [monad m] [is_lawful_monad m]
  (f : α → γ → β) (cmd : m α) (g : α → m γ) :
  cmd >>= (λ x, f x <$> g x) = do { x ← cmd, y ← g x, pure $ f x y }  :=
by congr; ext; rw [← bind_pure (g x),map_bind]; simp

@[functor_norm]
lemma bind_seq {α β γ : Type u} {m} [monad m] [is_lawful_monad m]
  (f : α → m (γ → β)) (cmd : m α) (g : α → m γ) :
  cmd >>= (λ x, f x <*> g x) = do { x ← cmd, h ← f x, y ← g x, pure $ h y }  :=
by congr; ext; simp [seq_eq_bind_map] with functor_norm

end monad

attribute [functor_norm] bind_assoc has_bind.and_then map_bind seq_left_eq seq_right_eq

namespace sum

variables {e : Type v} {α β : Type u}

protected def seq : Π (x : sum e (α → β)) (f : sum e α), sum e β
| (sum.inl e) _ := sum.inl e
| (sum.inr f) x := f <$> x

instance : applicative (sum e) :=
{ seq := @sum.seq e,
  pure := @sum.inr e }

instance : is_lawful_applicative (sum e) :=
by constructor; intros;
   casesm* _ ⊕ _; simp [(<*>),sum.seq,pure,(<$>)];
   refl

end sum

namespace functor
def foldl (α : Type u) (β : Type v) := α → α
def foldr (α : Type u) (β : Type v) := α → α

instance foldr.applicative {α} : applicative (foldr α) :=
{ pure := λ _ _, id,
  seq := λ _ _ f x, f ∘ x }

instance foldl.applicative {α} : applicative (foldl α) :=
{ pure := λ _ _, id,
  seq := λ _ _ f x, x ∘ f }

instance foldr.is_lawful_applicative {α} : is_lawful_applicative (foldr α) :=
by refine { .. }; intros; refl

instance foldl.is_lawful_applicative {α} : is_lawful_applicative (foldl α) :=
by refine { .. }; intros; refl

def foldr.eval {α β} (x : foldr α β) : α → α := x

def foldl.eval {α β} (x : foldl α β) : α → α := x

def foldl.cons {α β} (x : α) : foldl (list α) β :=
list.cons x

def foldr.cons {α β} (x : α) : foldr (list α) β :=
list.cons x

def foldl.cons' {α} (x : α) : foldl (list α) punit :=
list.cons x

def foldl.lift {α} (x : α → α) : foldl α punit := x
def foldr.lift {α} (x : α → α) : foldr α punit := x

end functor

instance {α : Type u} : traversable (prod.{u u} α) :=
{ map := λ β γ f (x : α × β), prod.mk x.1 $ f x.2,
  traverse := λ m _ β γ f (x : α × β), by exactI prod.mk x.1 <$> f x.2 }

namespace traversable

variables {t : Type u → Type u} [traversable t]

def to_list {α} (x : t α) : list α :=
@functor.foldr.eval _ (t punit) (traverse functor.foldr.cons x) []

end traversable

/-
namespace name

def append_suffix : name → string → name
| (mk_string s n) s' := mk_string (s ++ s') n
| n _ := n

end name
-/

namespace level

meta def fold_mvar {α} : level → (name → α → α) → α → α
| zero f := id
| (succ a) f := fold_mvar a f
| (param a) f := id
| (mvar a) f := f a
| (max a b) f := fold_mvar a f ∘ fold_mvar b f
| (imax a b) f := fold_mvar a f ∘ fold_mvar b f

end level

namespace expr

meta def replace_all (e : expr) (p : expr → Prop) [decidable_pred p] (r : expr) : expr :=
e.replace $ λ e i, guard (p e) >> pure (r.lift_vars 0 i)

meta def const_params : expr → list level
| (const _ ls) := ls
| _ := []

meta def collect_meta_univ (e : expr) : list name :=
native.rb_set.to_list $ e.fold native.mk_rb_set $ λ e' i s,
match e' with
| (sort u) := u.fold_mvar (flip native.rb_set.insert) s
| (const _ ls) := ls.foldl (λ s' l, l.fold_mvar (flip native.rb_set.insert) s') s
| _ := s
end

end expr

namespace tactic

meta def unify_univ (u u' : level) : tactic unit :=
unify (expr.sort u) (expr.sort u')

meta def add_decl' (d : declaration) : tactic expr :=
do add_decl d,
   pure $ expr.const d.to_name $ d.univ_params.map level.param

meta def renew : expr → tactic expr
| (expr.local_const uniq pp bi t) := mk_local' pp bi t
| e := fail format!"{e} is not a local constant"

meta def trace_error {α} (tac : tactic α) : tactic α :=
λ s, match tac s with
     | r@(result.success _ _) := r
     | (result.exception (some msg) pos s') := (trace (msg ()) >> result.exception (some msg) pos) s'
     | (result.exception none pos s') := (trace "no msg" >> result.exception none pos) s'
     end

meta def is_type (e : expr) : tactic bool :=
do (expr.sort _) ← infer_type e | pure ff,
   pure tt

meta def list_macros : expr → list (name × list expr) | e :=
e.fold [] (λ m i s,
  match m with
  | (expr.macro m args) := (expr.macro_def_name m, args) :: s
  | _ := s end)

meta def expand_untrusted (tac : tactic unit) : tactic unit :=
do tgt ← target,
   mv  ← mk_meta_var tgt,
   gs ← get_goals,
   set_goals [mv],
   tac,
   env ← get_env,
   pr ← env.unfold_untrusted_macros <$> instantiate_mvars mv,
   set_goals gs,
   exact pr

meta def binders : expr → tactic (list expr)
| (expr.pi n bi d b) :=
  do v ← mk_local' n bi d,
     (::) v <$> binders (b.instantiate_var v)
| _ := pure []

meta def rec_args_count (t c : name) : tactic ℕ :=
do ct ← mk_const c >>= infer_type,
   (list.length ∘ list.filter (λ v : expr, v.local_type.is_app_of t)) <$> binders ct

meta def match_induct_hyp (n : name) : list expr → list expr → tactic (list $ expr × option expr)
| [] [] := pure []
| [] _ := fail "wrong number of inductive hypotheses"
| (x :: xs) [] := (::) (x,none) <$> match_induct_hyp xs []
| (x :: xs) (h :: hs) :=
do t ← infer_type x,
   if t.is_app_of n
     then (::) (x,h) <$> match_induct_hyp xs hs
     else (::) (x,none) <$> match_induct_hyp xs (h :: hs)

meta def is_recursive_type (n : name) : tactic bool :=
do e ← get_env,
   let cs := e.constructors_of n,
   rs ← cs.mmap (rec_args_count n),
   pure $ rs.any (λ r, r > 0)

meta def better_induction (e : expr) : tactic $ list (name × list (expr × option expr) × list (name × expr)) :=
do t ← infer_type e,
   let tn := t.get_app_fn.const_name,
   focus1 $
   do vs ← induction e,
      gs ← get_goals,
      vs' ← mzip_with (λ g (pat : name × list expr × list (name × expr)),
        do let ⟨n,args,σ⟩ := pat,
           set_goals [g],
           nrec ← rec_args_count tn n,
           let ⟨args,rec⟩ := args.split_at (args.length - nrec),
           args ← match_induct_hyp tn args rec,
           pure ((n,args,σ))) gs vs,
      set_goals gs,
      pure vs'

meta def extract_def' {α} (n : name) (trusted : bool) (elab_def : tactic α) : tactic α :=
do cxt ← list.map to_implicit <$> local_context,
   t ← target,
   (r,d) ← solve_aux t elab_def,
   d ← instantiate_mvars d,
   t' ← pis cxt t,
   d' ← lambdas cxt d,
   let univ := t'.collect_univ_params,
   add_decl $ declaration.defn n univ t' d' (reducibility_hints.regular 1 tt) trusted,
   r <$ (applyc n; assumption)

open expr list nat

meta def remove_intl_const : expr → tactic expr
| v@(local_const uniq pp bi _) :=
  do t ← infer_type v,
     pure $ local_const uniq pp bi t
| e := pure e

meta def intron' : ℕ → tactic (list expr)
| 0 := pure []
| (succ n) := (::) <$> intro1 <*> intron' n

meta def unpi : expr → tactic (list expr × expr)
| (pi n bi d b) :=
  do v ← mk_local' n bi d,
     prod.map (cons v) id <$> unpi (b.instantiate_var v)
| e := pure ([],e)

meta def unify_app_aux : expr → expr → list expr → tactic expr
| e (pi _ _ d b) (a :: as) :=
do t ← infer_type a,
   unify t d,
   e' ← head_beta (e a),
   b' ← whnf (b.instantiate_var a),
   unify_app_aux e' b' as
| e t (_ :: _) := fail "too many arguments"
| e _ [] := pure e

meta def unify_app (e : expr) (args : list expr) : tactic expr :=
do t ← infer_type e >>= whnf,
   unify_app_aux e t args

end tactic

namespace tactic.interactive

open lean lean.parser interactive interactive.types tactic

local postfix `*`:9000 := many

meta def clear_except (xs : parse ident *) : tactic unit :=
do let ns := name_set.of_list xs,
   local_context >>= mmap' (λ h : expr,
     when (¬ ns.contains h.local_pp_name) $
       try $ tactic.clear h) ∘ list.reverse

meta def splita := split; [skip, assumption]

@[hole_command]
meta def whnf_type_hole : hole_command :=
{ name := "Reduce expected type",
  descr := "Reduce expected type",
  action := λ es,
    do t ← match es with
           | [h] := to_expr h >>= infer_type >>= whnf
           | [] := target >>= whnf
           | _ := fail "too many expressions"
           end,
       trace t,
       pure [] }

end tactic.interactive
