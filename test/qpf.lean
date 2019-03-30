
import data.fix.parser.basic

universes u

namespace hidden

universes u_1 u_2 u_3

set_option trace.app_builder true
set_option pp.universes true

qpf list_F'' (α β : Type)
| cons : ℤ → (ℕ → α) → (list ℕ → α) → (ℤ → β) → list_F''
| a : α → list_F''
| b : β → list_F''
| nil : list_F''
-- #exit
-- @[derive mvqpf]
qpf list_F (α : Type)
| nil : list_F
| cons : ℤ → α → list_F

-- #exit
-- -- #print hidden.list_F.head_t
-- #print prefix hidden.list_F
-- #print hidden.list_F.child_t
-- -- #print hidden.list_F.pfunctor

-- -- #test list_F.internal_eq
-- -- #test @list_F.map

-- example : ∀ (α : Type), list_F.internal (typevec.of_ind (typevec.ind.cons α typevec.ind.nil)) = list_F α :=
-- list_F.internal_eq

-- example : Π (α β : typevec 1), α ⟹ β → list_F.internal α → list_F.internal β :=
-- list_F.internal.map

-- -- #test hidden.list_F.internal.map._equation_0
-- -- #test hidden.list_F.internal.map._equation_1

-- example : ∀ (α α' : Type) (f0 : α → α'),
--   list_F.internal.map (typevec.of_ind (typevec.ind.cons α typevec.ind.nil))
--       (typevec.of_ind (typevec.ind.cons α' typevec.ind.nil))
--       (typevec.append_fun typevec.nil_fun f0)
--       _ =
--     list_F.nil α' :=
-- list_F.internal.map._equation_0

-- example : ∀ (α α' : Type) (f0 : α → α') (a : ℤ) (a_1 : α),
--   list_F.internal.map (typevec.of_ind (typevec.ind.cons α typevec.ind.nil))
--       (typevec.of_ind (typevec.ind.cons α' typevec.ind.nil))
--       (typevec.append_fun typevec.nil_fun f0)
--       _ =
--     list_F.cons a (f0 a_1) :=
-- list_F.internal.map._equation_1


-- @[derive mvqpf]

-- @[user_command]
-- meta def my_cmd (_ : interactive.parse (lean.parser.tk "my_cmd")) : lean.parser unit :=
-- do lean.parser.with_input lean.parser.command_like
-- "inductive list_F (a : Type)
-- | nil : list_F",
--    pure ().

-- my_cmd

-- #check @list_F.no_confusion

-- -- #print hidden.list_F'.head_t
-- -- #print hidden.list_F'.child_t.α
-- -- #print hidden.list_F'.child_t.β
-- -- #print hidden.list_F'.child_t
-- -- #print hidden.list_F'.pfunctor

-- -- #test list_F'.internal_eq
-- -- #test @list_F'.map

-- example : ∀ (α β : Type),
--   list_F'.internal (typevec.of_ind (typevec.ind.cons α (typevec.ind.cons β typevec.ind.nil))) = list_F' α β :=
-- list_F'.internal_eq

-- example : Π (α β : typevec 2), α ⟹ β → list_F'.internal α → list_F'.internal β :=
-- list_F'.internal.map

-- -- #test hidden.list_F'.internal.map._equation_0
-- -- #test hidden.list_F'.internal.map._equation_1

-- example : ∀ (α β α' β' : Type) (f0 : α → α') (f1 : β → β'),
--   list_F'.internal.map (typevec.of_ind (typevec.ind.cons α (typevec.ind.cons β typevec.ind.nil)))
--       (typevec.of_ind (typevec.ind.cons α' (typevec.ind.cons β' typevec.ind.nil)))
--       (typevec.append_fun (typevec.append_fun typevec.nil_fun f1) f0)
--       _ =
--     list_F'.nil α' β' :=
-- list_F'.internal.map._equation_0

-- example : ∀ (α β α' β' : Type) (f0 : α → α') (f1 : β → β') (a : α) (a_1 : β),
--   list_F'.internal.map (typevec.of_ind (typevec.ind.cons α (typevec.ind.cons β typevec.ind.nil)))
--       (typevec.of_ind (typevec.ind.cons α' (typevec.ind.cons β' typevec.ind.nil)))
--       (typevec.append_fun (typevec.append_fun typevec.nil_fun f1) f0)
--       _ =
--     list_F'.cons (f0 a) (f1 a_1) :=
-- list_F'.internal.map._equation_1
set_option trace.app_builder true
set_option pp.universes true

-- @[derive mvqpf]
qpf list_F''_ (α β γ : Type u)
| nil : (β → γ) → list_F''_
| cons : (α → β) → list_F''_

-- #exit
-- #print hidden.list_F''.head_t
-- #print hidden.list_F''.child_t.γ
-- #print hidden.list_F''.child_t
-- #print hidden.list_F''.pfunctor

-- #check list_F''.internal_eq
-- #check @list_F''.map

-- example : ∀ (α : Type*) (β : Type*) (γ : Type*),
--     list_F''.internal α β (typevec.of_ind (typevec.ind.cons γ typevec.ind.nil)) = list_F'' α β γ :=
-- list_F''.internal_eq

-- example : Π (α : Type*) (β : Type*) (α_1 β_1 : typevec 1),
--     α_1 ⟹ β_1 → list_F''.internal α β α_1 → list_F''.internal α β β_1 :=
-- @list_F''.internal.map

-- #test hidden.list_F''.internal.map._equation_0
-- #test hidden.list_F''.internal.map._equation_1

-- #check list_F''.internal.map

-- example : ∀ (α : Type u_1) (β : Type u_1) (γ γ' : Type u_1) (f2 : γ → γ') (a : β → γ),
--   list_F''.internal.map α β (typevec.of_ind (typevec.ind.cons γ typevec.ind.nil))
--       (typevec.of_ind (typevec.ind.cons γ' typevec.ind.nil))
--       (typevec.append_fun typevec.nil_fun f2)
--       _ =
--     list_F''.nil α (λ (a_1 : β), f2 (a a_1)) :=
-- list_F''.internal.map._equation_0

-- example : ∀ (α : Type u_1) (β : Type u_1) (γ γ' : Type u_1) (f2 : γ → γ') (a : α → β),
--   list_F''.internal.map α β (typevec.of_ind (typevec.ind.cons γ typevec.ind.nil))
--       (typevec.of_ind (typevec.ind.cons γ' typevec.ind.nil))
--       (typevec.append_fun typevec.nil_fun f2)
--       _ =
--     list_F''.cons γ' (λ (a_1 : α), a a_1) :=
-- list_F''.internal.map._equation_1

-- @[derive mvqpf]
qpf list_F''' (α β γ : Type u)
| nil : list_F'''
| cons : (γ → β) → list_F'''

-- #check hidden.list_F'''.pfunctor.cons

-- #exit
-- #print hidden.list_F'''.head_t
-- #print hidden.list_F'''.child_t.α
-- #print hidden.list_F'''.child_t.β
-- #print hidden.list_F'''.child_t
-- #print hidden.list_F'''.pfunctor

-- #check list_F'''.internal_eq
-- #check @list_F'''.map

-- example : ∀ (α β γ : Type*),
--     list_F'''.internal γ (typevec.of_ind (typevec.ind.cons α (typevec.ind.cons β typevec.ind.nil))) =
--       list_F''' α β γ :=
-- list_F'''.internal_eq

-- example : Π (γ : Type*) (α β : typevec 2), α ⟹ β → list_F'''.internal γ α → list_F'''.internal γ β :=
-- @list_F'''.internal.map

-- -- #test hidden.list_F'''.internal.map._equation_0
-- -- #test hidden.list_F'''.internal.map._equation_1

-- example : ∀ (α β γ α' β' : Type u) (f0 : α → α') (f1 : β → β'),
--   list_F'''.internal.map γ (typevec.of_ind (typevec.ind.cons α (typevec.ind.cons β typevec.ind.nil)))
--       (typevec.of_ind (typevec.ind.cons α' (typevec.ind.cons β' typevec.ind.nil)))
--       (typevec.append_fun (typevec.append_fun typevec.nil_fun f1) f0)
--       _ = --(list_F'''.nil α β γ) =
--     list_F'''.nil α' β' γ :=
-- list_F'''.internal.map._equation_0

-- example : ∀ (α β γ α' β' : Type u) (f0 : α → α') (f1 : β → β') (a : γ → β),
--   list_F'''.internal.map γ (typevec.of_ind (typevec.ind.cons α (typevec.ind.cons β typevec.ind.nil)))
--       (typevec.of_ind (typevec.ind.cons α' (typevec.ind.cons β' typevec.ind.nil)))
--       (typevec.append_fun (typevec.append_fun typevec.nil_fun f1) f0)
--       ( _ ) =
--     list_F'''.cons α' (λ (a_1 : γ), f1 (a a_1)) :=
-- list_F'''.internal.map._equation_1

-- @[derive mvqpf]
qpf list_F'''' (α β γ : Type u)
| nil : (β → γ) → (γ → α) → list_F''''
| cons : (α → β) → list_F''''

-- #print prefix hidden.list_F''''
-- #check hidden.list_F''''.pfunctor.cons

-- #print hidden.list_F''''.head_t
-- #print hidden.list_F''''.child_t
-- #print hidden.list_F''''.pfunctor

-- #check @list_F''''.internal_eq
-- #check @list_F''''.internal.map

-- example : ∀ (α : Type*) (β : Type*) (γ : Type*),
--     list_F''''.internal α β γ (typevec.of_ind typevec.ind.nil) = list_F'''' α β γ :=
-- @list_F''''.internal_eq

example : Π (α : Type*) (β : Type*) (γ : Type*) (α_1 β_1 : typevec 0),
    α_1 ⟹ β_1 → list_F''''.internal α β γ α_1 → list_F''''.internal α β γ β_1 :=
@list_F''''.internal.map

-- #test hidden.list_F''''.internal.map._equation_0

example : ∀ (α : Type u_1) (β : Type u_1) (γ : Type u_1) (a : β → γ) (a_1 : γ → α),
  list_F''''.internal.map α β γ ⦃ ⦄ ⦃ ⦄ typevec.nil_fun
      _ =
    list_F''''.nil (λ (a_1 : β), a a_1) (λ (a : γ), a_1 a) :=
list_F''''.internal.map._equation_0

example : ∀ (α : Type u_1) (β : Type u_1) (γ : Type u_1) (a : α → β),
  list_F''''.internal.map α β γ (⦃ ⦄) ( ⦃ ⦄ ) typevec.nil_fun
      _ =
    list_F''''.cons γ (λ (a_1 : α), a a_1) :=
list_F''''.internal.map._equation_1

-- data list
-- | nil : list
-- | cons : ℤ → list → list

end hidden
