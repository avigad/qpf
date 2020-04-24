import data.fix.parser.equations
import data.lazy_list

namespace serial

codata parser (α β : Type)
| pure : β → parser
| read : (α → parser) → parser

#check parser.read

def patch {α β} : lazy_list α → parser α β → option β
| lazy_list.nil x := parser.cases_on x (λ a, some a) (λ _, none)
| (lazy_list.cons x xs) f :=
  parser.cases_on f (λ a,  none)
    (λ f, patch (xs ()) (f x))

infix ` >-> `:55 := patch

-- too much explicit stuff
section bisim
variables {α β : Type}
variables (r : parser α β → parser α β → Prop)
variables
  (hh₀₀ : ∀ (x y : β),
    r (parser.pure _ _ x) (parser.pure _ _ y) → x = y)
  (hh₀₁ : ∀ (x : β) (y : α → parser α β),
    r (parser.pure _ _ x) (parser.read _ _ y) → false)
  (hh₁₀ : ∀ (x : α → parser α β) (y : β),
    r (parser.read _ _ x) (parser.pure _ _ y) → false)
  (hh₁₁ : ∀ (x y : α → parser α β),
    r (parser.read _ _ x) (parser.read _ _ y) → ∀ i, r (x i) (y i))

include hh₀₀ hh₀₁ hh₁₀ hh₁₁

-- generate me
lemma parser.bisim₂ :
  ∀ (x y : parser α β), r x y → x = y :=
sorry

end bisim

namespace bisim₃

variables {α α' β β' : Type}
variables (fn : parser α β → parser α β)
variables
  (hh₀₀ : ∀ (x y : β),
    r (parser.pure _ _ x) (parser.pure _ _ y) → x = y)
  (hh₀₁ : ∀ (x : β) (y : α → parser α β),
    r (parser.pure _ _ x) (parser.read _ _ y) → false)
  (hh₁₀ : ∀ (x : α → parser α β) (y : β),
    r (parser.read _ _ x) (parser.pure _ _ y) → false)
  (hh₁₁ : ∀ (x y : α → parser α β),
    r (parser.read _ _ x) (parser.read _ _ y) → ∀ i, r (x i) (y i))

lemma parser.bisim₂ :
  ∀ (x y : parser α β), r x y → x = y :=
sorry

end bisim₃


protected def bind {α β γ : Type} : parser α β → (β → parser α γ) → parser α γ
| x f :=
parser.corec' _ _ _
  (λ a : parser α β,
    parser.cases_on a
      (λ b, parser.shape.map id sum.inl $ mvqpf.cofix.dest (f b))
      (λ g, parser.shape.read $ λ a, sum.inr $ g a)) x

-- todo: generate me
lemma bind_eqn_1 {α β γ : Type} (x : α) (f : α → parser β γ) :
  serial.bind (parser.pure _ _ x) f =  f x :=
begin
  rw [serial.bind], apply mvqpf.cofix.ext,
  delta parser.corec', rw mvqpf.cofix.dest_corec',
end

-- todo: generate me
lemma bind_eqn_2 {α β γ : Type} (f : α → parser α β) (g : β → parser α γ) :
  serial.bind (parser.read _ _ f) g =  parser.read _ _ (λ x, serial.bind (f x) g) :=
sorry

instance parser.monad {α : Type} : monad (parser α) :=
{ pure := parser.pure _,
  bind := λ β γ : Type, serial.bind }

lemma pure_bind {α β γ} (x : α) (f : α → parser β γ) : pure x >>= f = f x :=
bind_eqn_1 _ _

/-
Note: no confusion is hard to use
Note: no_confusion lemmas
-/
-- generate this
@[simp]
lemma no_confusion_pure_pure {α β} (x y : β) :
  parser.pure α β x = parser.pure α β y ↔ x = y :=
begin
  split; intro h,
  { have := @parser.no_confusion _ _ (x = y) _ _ h,
    delta parser.no_confusion_type at this, revert this,
    simp [parser.cases_on_pure,parser.cases_on_read] },
  { rw h }
end

-- generate this
@[simp]
lemma no_confusion_pure_read {α β} (x : β) (y : α → parser α β) :
  parser.pure α β x = parser.read α β y ↔ false :=
begin
  split; intro h,
  { have := @parser.no_confusion _ _ false _ _ h,
    delta parser.no_confusion_type at this, revert this,
    simp [parser.cases_on_pure,parser.cases_on_read] },
  { cases h }
end

-- generate this
@[simp]
lemma no_confusion_read_pure {α β} (x : α → parser α β) (y : β) :
  parser.read α β x = parser.pure α β y ↔ false :=
begin
  split; intro h,
  { have := @parser.no_confusion _ _ false _ _ h,
    delta parser.no_confusion_type at this, revert this,
    simp [parser.cases_on_pure,parser.cases_on_read] },
  { cases h }
end

-- generate this
@[simp]
lemma no_confusion_read_read {α β} (x y : α → parser α β) :
  parser.read α β x = parser.read α β y ↔ x = y :=
begin
  split; intro h,
  { have := @parser.no_confusion _ _ (x = y) _ _ h,
    delta parser.no_confusion_type at this, revert this,
    simp [parser.cases_on_pure,parser.cases_on_read] },
  { rw h }
end

lemma bind_pure {α β} (x : parser α β) : x >>= pure = x :=
begin
  let R := (λ a b, a = b ∨ ∃ (x : α → parser α β), a = parser.read _ _ x >>= pure ∧ b = parser.read _ _ x),
  apply parser.bisim₂ R _ _ _ _ _ _ _;
  dsimp [R]; clear R,
  { intros a b, simp },
  { intros a b, simp [(>>=),serial.bind_eqn_2], },
  { intros a b, simp, },
  { intros a b, simp [(>>=),serial.bind_eqn_2],
    rintros (H|H) i,
    { subst H, left, refl },
    { replace H := congr_fun H i, revert H,
      dsimp, generalize : a i = a', generalize : b i = b',
      clear a b i,
      refine parser.cases_on a' _ _;
      refine parser.cases_on b' _ _,
      { simp [serial.bind_eqn_1,pure], },
      { simp [serial.bind_eqn_2,pure], },
      { simp [serial.bind_eqn_1,pure], },
      { simp [serial.bind_eqn_1,serial.bind_eqn_2,pure],
        introv h, right, exact h, }, } },
  { refine parser.cases_on x _ _,
    { simp [serial.bind_eqn_1,(>>=),pure], },
    { simp [serial.bind_eqn_1,(>>=),pure], }, }
end

lemma bind_assoc {ι α β γ} (x : parser ι α)
  (f : α → parser ι β)
  (g : β → parser ι γ) : x >>= f >>= g = x >>= (λ a, f a >>= g) :=
begin
  let R := (λ a b, a = b ∨
    ∃ (x : ι → parser ι α),
      a = parser.read _ _ x >>= f >>= g ∧
      b = parser.read _ _ x >>= (λ a, f a >>= g)),
  apply parser.bisim₂ R _ _ _ _ _ _ _;
  dsimp [R]; clear R,
  { intros a b, simp [(>>=),serial.bind_eqn_2], },
  { intros a b, simp [(>>=),serial.bind_eqn_2], },
  { intros a b, simp [(>>=),serial.bind_eqn_2], },
  { intros a b, simp [(>>=),serial.bind_eqn_2],
    rintro (H|H) i,
    { subst H, left, refl },
    { revert H, simp, introv Ha Hb,
      replace Ha := congr_fun Ha i, revert Ha,
      replace Hb := congr_fun Hb i, revert Hb,
      dsimp, refine parser.cases_on (x_1 i) _ _,
      { simp [serial.bind_eqn_1], introv Ha Hb,
        left, rw [Ha,Hb] },
      { simp [serial.bind_eqn_2], intros ff Ha Hb,
        right, existsi ff, rw [← Ha,← Hb], exact ⟨rfl,rfl⟩ } } },
  { refine parser.cases_on x _ _,
    { simp [serial.bind_eqn_1,(>>=),pure], },
    { simp [serial.bind_eqn_1,serial.bind_eqn_2,(>>=),pure],
      intros ff, right, refine ⟨ff,rfl,rfl⟩, }, }
end

def read {α} : parser α α :=
parser.read _ _ $ parser.pure _ _

lemma read_def {α β} (pars₁ : α → parser α β) :
  read >>= pars₁ = parser.read _ _ pars₁ :=
by dsimp [(>>=)]; rw [read,serial.bind_eqn_2];
   congr; ext; rw serial.bind_eqn_1

lemma compose_cons {α β}
  (x : α)
  (ser₀ : thunk $ lazy_list α)
  (pars₁ : α → parser α β) :
  @lazy_list.cons α x ser₀ >-> parser.read _ _ pars₁ =
  ser₀ () >-> pars₁ x :=
begin
  generalize h : ser₀ () = ser₁,
  replace h : ser₀ = λ _, ser₁,
  { ext ⟨ ⟩, exact h },
  subst h,
  rw [(>->),parser.cases_on_read],
end

lemma compose_cons' {α β}
  (x : α)
  (ser₀ : thunk $ lazy_list α)
  (pars₁ : α → parser α β) :
  @lazy_list.cons α x ser₀ >-> (read >>= pars₁) =
  ser₀ () >-> pars₁ x :=
by rw [read_def,compose_cons]

lemma compose {α β γ}
  (ser₀ ser₁ : lazy_list α)
  (pars₀ : parser α β)
  (pars₁ : β → parser α γ)
  (r₀ : β) (r₁ : γ)
  (h₀ : ser₀ >-> pars₀ = some r₀)
  (h₁ : ser₁ >-> pars₁ r₀ = some r₁) :
  ser₀.append ser₁ >-> (pars₀ >>= pars₁) = some r₁ :=
begin
  induction ser₀ generalizing pars₀,
  { rw [(>->)] at h₀,
    revert pars₀, intro,
    apply parser.cases_on pars₀; intros,
    { rw parser.cases_on_pure at h₀, cases h₀,
      erw [lazy_list.append,pure_bind], exact h₁, },
    { rw parser.cases_on_read at h₀, cases h₀ } },
  { rw [(>->)] at h₀,
    revert pars₀, intro,
    apply parser.cases_on pars₀; intros,
    { rw parser.cases_on_pure at h₀, cases h₀, },
    { rw parser.cases_on_read at h₀,
      rwa [lazy_list.append,← read_def,bind_assoc,compose_cons',ser₀_ih] } },
end

namespace parser
open function

def forever {α β} (f : α → parser α β) : parser α β :=
parser.corec' _ _ _
  (λ g : α → parser α β,
  shape.read $ λ a,
    parser.cases_on (g a)
      (λ b, sum.inr f)
      (λ g, sum.inr g))
  f

lemma forever_def {α β} (f : α → parser α β) :
  forever f = serial.read >>= f >> forever f :=
sorry

/-

codef feed {α β γ} (a : α → parser α β) : (α → parser α β) → parser β γ → parser α γ
| f (read g) := read $ λ x,
  match f x with
  | pure y := feed a $ g y
  | read f := feed f (read g)
  end
| _ (pure x) := pure x
-/

def feed_aux {α β γ} (x₀ x : α → parser α β) (y : parser β γ) : parser α γ :=
parser.cases_on y
  (λ ay, pure _ _ ay)
  (λ fy,
parser.corec' _ _ _
  (uncurry $ λ (x : α → parser α β) (y : β → parser β γ),
    shape.read $ λ a,
      parser.cases_on (x a)
        (λ b, parser.cases_on (y b)
           (sum.inl ∘ pure _ _)
           (λ y', sum.inr (x₀,y')))
        (λ x', sum.inr (x',y)))
  (x,fy))

def feed {α β γ} (x₀ : α → parser α β) (y : parser β γ) : parser α γ :=
feed_aux x₀ x₀ y

lemma feed_def_0 {α β γ} (x₀ x : α → parser α β) (y : β → parser β γ) :
  feed_aux x₀ x (read _ _ y) =
  read _ _ (λ a,
    parser.cases_on (x₀ a)
      (λ b, feed_aux x₀ x₀ (y b))
      (λ x', feed_aux x₀ x' (read _ _ y)) ) :=
sorry

lemma feed_def_1 {α β γ} (x₀ x : α → parser α β) (r : γ) :
  feed_aux x₀ x (pure _ _ r) =
  pure _ _ r :=
sorry

#check @parser.cases_on
#exit
end parser


structure channel (α β : Type) :=
(serialize : α → lazy_list β)
(parse : parser β α)
(inverse : ∀ x, serialize x >-> parse = some x)

namespace channel

def comp {α β γ} (x : channel α β) (y : channel β γ) : channel α γ :=
{ serialize := x.serialize >=> y.serialize,
  parse := _ }

end channel


namespace nat

variables (n : ℕ) (hn : n > 1)

def serialize : ℕ → lazy_list (fin n)
| i :=
  have hn' : n > 0, from lt_trans zero_lt_one hn,
    lazy_list.cons ⟨i % n, nat.mod_lt _ hn'⟩ $
    if h' : i > 0 then
      have i / n < i, from nat.div_lt_self h' hn,
      serialize (i / n)
    else lazy_list.nil

def parse' : ℕ → parser (fin n) ℕ :=
parser.corec' _ _ _ (λ i,
parser.shape.read $ λ x,
  if x.val = 0
    then sum.inl (parser.pure _ _ i)
    else sum.inr (i * n + x.val))

def parse : parser (fin n) ℕ :=
parse' n 0

lemma parse_def (i : ℕ) :
  parse' n i =
  do x ← read,
     if x.val = 0
       then pure i
       else parse' n (i * n + x.val) :=
sorry

lemma correctness (i j : ℕ) :
  serialize n hn i >-> parse' n j = some (i + j) :=
begin
  induction i using nat.strong_induction_on,
  rw [serialize,parse_def], simp [compose_cons'],
end

end nat


end serial
