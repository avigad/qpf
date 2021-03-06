import data.fix.parser.equations

universes u

data tree (α β : Type)
| nil : tree
| cons : α → (β → tree) → tree

-- #print prefix tree
-- #print tree.shape
-- #print tree.shape.internal
-- #print tree.shape.internal.mvfunctor
-- #print tree.shape.internal.mvqpf
-- #print tree.internal
-- #print tree
-- #print tree.mvfunctor
-- #print tree.mvqpf
-- #check tree.nil
-- #check tree.cons
-- #check @tree.cases_on
-- #check @tree.rec
-- #check @tree.drec

codata tree' (α β : Type)
| nil : tree'
| cons : α → (β → tree') → tree'

-- #print prefix tree'
-- #print tree'.shape
-- #print tree'.shape.internal
-- #print tree'.shape.internal.mvfunctor
-- #print tree'.shape.internal.mvqpf
-- #print tree'.internal
-- #print tree'
-- #print tree.mvfunctor
-- #print tree.mvqpf
-- #check tree'.nil
-- #check tree'.cons
-- #check @tree'.cases_on
-- #check @tree'.corec
-- #check @tree'.bisim
