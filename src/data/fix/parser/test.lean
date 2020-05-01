import .defn

#eval 3 .

codata part (α : Type)
| pure : α → part
| delay : part → part

-- #print part._ctors
-- set_option trace.app_builder true

-- codef diverge'' {α} : ℕ → list ℕ → ℤ → part α
-- | x xs k :=
-- part.delay  (diverge'' x.succ (x :: xs) k)

-- #print prefix   diverge''
-- set_option trace.auto.finish true
-- set_option trace.simp_lemmas.invalid true

codef diverge' {α} : part α :=
part.delay diverge'

-- #print prefix part.corec₁

-- #print prefix diverge'

-- def diverge {α} : part α :=
-- part.corec _ unit (λ _, part.shape.delay ()) ()

-- run_cmd do
-- t ← tactic.get_eqn_lemmas_for tt ff ``diverge',
-- tactic.trace t,
-- t ← tactic.interactive.get_rule_eqn_lemmas (tactic.interactive.rw_rule.mk ⟨0,0⟩ tt ``(diverge')),
-- tactic.trace t,
-- t ← tactic.interactive.get_rule_eqn_lemmas (tactic.interactive.rw_rule.mk ⟨0,0⟩ tt ``(diverge')),
-- tactic.trace t

-- example {α} (x : part α) : x = diverge :=
-- by rw diverge

-- example {α} (x : part α) : x = diverge' :=
-- by rw diverge'

-- example {α} (x : part α) : x = diverge' :=
-- by simp  [diverge']

-- example {α} (x : part α) : x = diverge' :=
-- by do
-- { t ← tactic.get_eqn_lemmas_for tt ff ``diverge',
--   t ← t.mmap tactic.mk_const,
--   t.mmap tactic.infer_type >>= tactic.trace,
--   tactic.trace_state,
--   t.mmap' tactic.rewrite_target }

-- #exit

codata str (α : Type)
| nil : str
| cons : α → str → str

-- -- hole errors wrong place
-- -- compile pattern matching on codata
-- codef map {α β} (f : α → β) : str α → str β
-- | s := str.cases_on s str.nil (λ x xs, str.cons (f x) (map xs))

section
-- set_option trace.debug.eqn_compiler.structural_rec true
-- set_option trace.eqn_compiler true
-- set_option trace.qpf true

attribute [pattern] str.cons
-- #print str.cons
def map' {α β} (f : α → β) : list α → str β
| [] := str.nil
| (list.cons x xs) := str.cons (f x) (map' xs)

-- codef map' {α β} (f : α → β) : list α → str β
-- | [] := str.nil
-- | (list.cons x xs) := str.cons (f x) (map' xs)

-- codef map {α β} (f : α → β) : str α → str β
-- | (str.cons x xs) := str.cons (f x) (map xs)
-- | str.nil := str.nil
end

-- codef map' {α β} (f : α → β) : list α → str β
-- | [] := str.nil
-- | (x :: xs) := str.cons (f x) (map' xs)

-- weird behavior if `str.cons x $ enum_from x.succ`
codef enum_from : ℕ → str ℕ
| x := str.cons x (enum_from x.succ)

-- #exit
-- #check part.bisim_rel

-- #check @mvqpf.cofix.bisim
-- #check part.shape.liftr
-- #print part.shape.liftr
-- #print prefix part.shape

section bisim
variables {α : Type}
variables (r : part α → part α → Prop)
variables (hh : ∀ (x y : part α),
    r x y → part.shape.liftr eq r (mvqpf.cofix.dest x) (mvqpf.cofix.dest y))

-- generate me
lemma part.bisim
  (x y : part α) (hr : r x y) : x = y :=
mvqpf.cofix.bisim₂ r (λ x y hr, (part.shape.liftr_iff _ _ _ _).2 $ hh _ _ hr) _ _ hr

end bisim

section part

-- generate me
lemma part.shape.dest_pure {α} (x : α) :
  mvqpf.cofix.dest (part.pure x) = part.shape.pure x :=
mvqpf.cofix.dest_mk _

-- generate me
lemma part.shape.dest_delay {α} (x : part α) :
  mvqpf.cofix.dest (part.delay x) = part.shape.delay x :=
mvqpf.cofix.dest_mk _

end part

section bisim
variables {α : Type}
variables (r : part α → part α → Prop)
variables
  (hh₀₀ : ∀ (x y : α),
    r (part.pure x) (part.pure y) → x = y)
  (hh₀₁ : ∀ (x : α) (y : part α),
    r (part.pure x) (part.delay y) → false)
  (hh₁₀ : ∀ (x : part α) (y : α),
    r (part.delay x) (part.pure y) → false)
  (hh₁₁ : ∀ (x y : part α),
    r (part.delay x) (part.delay y) → r x y)

include hh₀₀ hh₀₁ hh₁₀ hh₁₁

-- generate me
lemma part.bisim₂ :
  ∀ (x y : part α), r x y → x = y :=
part.bisim _ $
begin
  intros x y, apply part.cases_on y; apply part.cases_on x,
  all_goals
  { intros a b hab,
    simp [part.shape.dest_pure,part.shape.dest_delay] },
  { constructor, apply hh₀₀ _ _ hab },
  { cases hh₁₀ _ _ hab },
  { cases hh₀₁ _ _ hab },
  { constructor, apply hh₁₁ _ _ hab },
end

end bisim

-- section corec

-- #check mvqpf.corecF
-- #check @part.corec

-- -- lemma part.corec_eq {α X : Type} (f : Π X, X → part.shape α X) (x₀ : X) :
-- --   part.corec _ _ (f X) x₀ = mvqpf.cofix.mk (f _ (part.corec _ _ (f X) x₀)) :=
-- -- begin
-- --   delta part.corec,
-- --   apply mvqpf.cofix.ext,
-- --   rw [mvqpf.cofix.dest_corec,mvqpf.cofix.dest_mk], dsimp, refl,
-- -- end

-- end corec

-- #print prefix mvqpf.cofix
-- #check @option.no_confusion
-- #check part.cases_on
-- #print prefix part
-- -- #exit
-- #print prefix part.shape.internal.map
-- #check mvfunctor.map

--| todo: generate this
-- example {α} : @diverge' α = part.delay diverge' :=
-- begin
--   apply mvqpf.cofix.ext,
--   rw [diverge,part.shape.dest_delay],
--   delta part.corec,
--   erw [mvqpf.cofix.dest_corec,← typevec.append_fun_id_id],
--   dsimp [mvfunctor.map],
--   convert part.shape.internal.map._equation_1 _ _ _,
--   ext i, cases i
-- end

-- #exit

-- example {α} : @diverge α = part.delay _ diverge :=
-- begin
--   -- conv { to_lhs, rw diverge, },
--   apply part.bisim₂ (λ x y, x = diverge ∧ y = part.delay _ diverge) _ _ _ _ _ _ ⟨rfl,rfl⟩;
--   dsimp;
--   rintro x y ⟨hx,hy⟩,
--   { have := @part.no_confusion _ (x=y) _ _ hy,
--     delta part.no_confusion_type at this,
--     rw [part.cases_on_pure,part.cases_on_delay] at this,
--     exact this, },
--   { have := @part.no_confusion _ false _ _ hx,
--     delta part.no_confusion_type at this,
--     rw [diverge,part.cases_on_pure,part.cases_on_delay] at this,
--     exact this, },
--  subst hx, subst hy,
-- end
-- #exit

-- codata str (α : Type)
-- | nil : str
-- | cons : α → str → str

-- #check str.shape.liftr_def
-- #check str.shape.liftr_iff

-- #check part.corec
-- #print prefix part
-- #print prefix mvqpf.cofix
-- #exit

-- def map {α β} (f : α → β) (x : str α) : str β :=
-- str.corec _ _
-- (λ x, @str.cases_on _ (λ _, str.shape β (str α)) x
--   str.shape.nil
--   (λ (x : α) (y : str α), str.shape.cons (f x) y))
-- x

-- -- todo: encapsulate data type in struct
-- lemma map_eqn_1 {α β} (f : α → β) (x : α) (xs : str α) :
--   map f (str.cons _ x xs) = str.cons _ (f x) (map f xs) :=
-- begin
--   dsimp [map],
--   apply mvqpf.cofix.ext,
--   erw [mvqpf.cofix.dest_corec,mvqpf.cofix.dest_mk],
--   dsimp, erw [str.cases_on_cons,← typevec.append_fun_id_id, typevec.eq_nil_fun typevec.id],
--   dsimp [(<$$>)],
--   erw [str.shape.internal.map._equation_1 id (mvqpf.cofix.corec _) _ _],
--   refl,
-- end

-- lemma map_eqn_2 {α β} (f : α → β) (x : α) (xs : str α) :
--   mvqpf.cofix.dest (map f (str.cons _ x xs)) = str.shape.cons (f x) (map f xs) :=
-- begin
--   rw [map], delta str.corec,
--   rw [mvqpf.cofix.dest_corec],
--   dsimp, rw str.cases_on_cons,
--   refl
-- end

-- def enum_from : ℕ → str ℕ :=
-- str.corec _ _ (λ x, str.shape.cons x x.succ)

lemma enum_from_eqn_1 (i : ℕ) : mvqpf.cofix.dest (enum_from i) = str.shape.cons i (enum_from i.succ) :=
begin
  rw [enum_from], symmetry, delta str.cons,
  rw [mvqpf.cofix.dest_mk], refl
end

-- lemma enum_from_eqn_2 (i : ℕ) : enum_from i = str.cons i (enum_from i.succ) :=
-- begin
--   rw [enum_from], symmetry, delta str.cons,
--   rw [mvqpf.cofix.dest_mk], refl
-- end

-- example {x y} : enum_from (x + y) = map (λ z, z + y) (enum_from x) :=
-- begin
--   bisim₂ x,
--   rw [Ha,Hb],
--   rw [typevec.rel_last',typevec.repeat_eq,typevec.drop,typevec.repeat_eq], -- typevec.split_fun,str.shape.liftr_iff],
--   erw [str.shape.liftr_iff,enum_from_eqn_1,enum_from_eqn_2 x],
--   simp [map_eqn_2],
--   constructor, refl,
--   refine ⟨x.succ,_,rfl⟩,
--   rw nat.succ_add,
-- end
