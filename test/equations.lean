
import data.fix.parser.equations

universes u

set_option trace.app_builder true
set_option pp.universes true

data list' (γ α β γ' : Type u) : Type u
| zero : γ → list'
| succ : γ' → α → (ℤ → β → list') → list'

-- #check list'.drec
-- #print list'.shape.internal.map

data nat'
| zero : nat'
| succ : nat' → nat'

-- #check nat'.drec
-- #print nat'.zero
-- #print nat'.succ

codata nat''
| zero : nat''
| succ : nat'' → nat''

-- -- #print nat'.internal
-- #print prefix nat''.corec
-- #print nat''.zero
-- #print nat''.succ

namespace hidden

data list (α : Type u) : Type u
| nil : list
| cons : α → list → list

-- #print hidden.list.internal
-- #print hidden.list
-- #print hidden.list.rec
-- #check @hidden.list.drec

codata stream (α : Type u) : Type u
| zero : stream
| succ : α → stream → stream

-- #print hidden.stream.internal
-- #print hidden.stream
-- #print hidden.stream.cases_on
-- #print hidden.stream.corec
-- #print hidden.stream.zero
-- #print hidden.stream.succ

codata stream' (γ α β γ' : Type u) : Type u
| zero : γ → stream'
| succ : γ' → α → (ℤ → β → stream') → stream'

-- #print hidden.stream'.internal
-- #print hidden.stream'
-- #check hidden.stream'.zero
-- #print hidden.stream'.cases_on
-- #check @hidden.stream'.succ
-- #print hidden.stream'.shape
-- #print hidden.stream'.corec
-- #print hidden.stream'.zero
-- #print hidden.stream'.succ

-- data list'' (α β : Type) : Type
-- | nil : list''
-- | cons : α → α → (β → list'') → list''

data list' (γ α β γ' : Type u) : Type u
| zero : γ → list'
| succ : γ' → α → (ℤ → β → list') → list'

-- #print hidden.list'.rec

data list'' (α β : Type) : Type
| nil : list''
| cons : α → (β → list'') → list''

-- -- Shape functor
-- inductive list.shape (α : Type) (β : Type) (X : Type) : Type
-- | nil : list.shape
-- | cons : α → (β → X) → list.shape

-- inductive list.shape.head_t (β : Type) : Type
-- | nil : list.shape.head_t
-- | cons : list.shape.head_t

-- inductive list.shape.child_t.α (β : Type) : list.shape.head_t β → Type
-- | cons_0 : list.shape.child_t.α (list.shape.head_t.cons β)

-- inductive list.shape.child_t.X (β : Type) : list.shape.head_t β → Type
-- | cons_0 : β → list.shape.child_t.X (list.shape.head_t.cons β)

-- #print hidden.list''.shape.child_t
-- def list.shape.child_t (β : Type) (hd : head_t β) : typevec 2 := ⦃ child_t.X β hd, child_t.α β hd ⦄

-- #print list''.shape.pfunctor
-- def list.shape.pfunctor (β : Type) : mvpfunctor 2 := {A := head_t β, B := child_t β}

-- #print list''.shape.internal
-- def list.shape.internal (β : Type) : typevec 2 → Type
-- | ⟨α,X,_⟩ := shape α β X

-- instance (β : Type) : mvfunctor (list.shape.internal β) := ...
-- instance (β : Type) : mvqpf (list.shape.internal β) := ...

-- def list.internal (β : Type) (v : typevec 1) : Type := fix (list.shape.internal β) v
-- def list (α β : Type) : Type := list.internal β ⦃ α ⦄

-- instance (β : Type) : mvfunctor (list.internal β) := ...
-- instance (β : Type) : mvqpf (list.internal β) := ...

-- -- Constructors
-- #print list''.nil
-- def list.nil (α β : Type) : list α β := ...

-- #print list''.cons
-- def list.cons (α β : Type) (x : α) (xs : β → list α β) : list α β := ...

-- -- Destructor
-- #print list''.cases_on
-- def list.cases_on {α β : Type} {C : list α β → Sort u_1} (n : list α β) :
--   C (list.nil α β) →
--   (Π (a : α) (a_1 : β → list α β), C (list.cons α β a a_1)) →
--   C n := ...

-- recursors
-- #print list''.rec
-- def list.rec {α β X : Type} : X → (α → (β → X) → X) → list α β → X := ...

-- #print list''.drec
-- def list.drec {α β : Type} {C : list α β → Sort u_1} :
--   C (list.nil α β) →
--   (Π (x : α) (xs : β → list α β), (Π i : β, C (xs i)) → C (list.cons α β x xs)) →
--   Π (n : list α β), C n := ...

-- codata stream₁ (α : Type u) : Type u
-- | zero : stream₁
-- | succ : α → (list stream₁) → stream₁

-- #print hidden.stream₁.internal
-- #print hidden.stream₁
-- #print hidden.stream₁.shape
-- #print hidden.stream₁.corec

end hidden
