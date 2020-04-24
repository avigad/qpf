import data.fix.parser.defn
.
#eval 3 .

codata llist (α : Type)
| nil : llist
| cons : α → llist → llist

inductive finite {α} : llist α → Prop
| nil : finite llist.nil
| cons (x : α) (xs : llist α) : finite xs → finite (llist.cons x xs)
def llistC (α β : Type) := llist α × β
def llistC' (α : typevec 2) : Type :=
llistC (typevec.last α) (typevec.last $ typevec.drop α)

def llistR{α β : Type} (xs ys : llistC α β) : Prop :=
xs.1 = ys.1 ∧ (finite xs.1 → xs.2 = ys.2)
