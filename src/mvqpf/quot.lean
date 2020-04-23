
import mvqpf.basic

universes u

namespace mvqpf

variables {n : ℕ}
variables {F : typevec.{u} n → Type u} [mvfunctor F] [q : mvqpf F]

section repr

variables {G : typevec.{u} n → Type u} [mvfunctor G]
variable  {FG_abs  : Π {α}, F α → G α}
variable  {FG_repr : Π {α}, G α → F α}

def quotient_qpf
    (FG_abs_repr : Π {α} (x : G α), FG_abs (FG_repr x) = x)
    (FG_abs_map  : ∀ {α β} (f : α ⟹ β) (x : F α), FG_abs (f <$$> x) = f <$$> FG_abs x) :
 mvqpf G :=
{ P := q.P,
  abs := λ α p, FG_abs (abs p),
  repr := λ α x, repr (FG_repr x),
  abs_repr := λ α x, by rw [abs_repr,FG_abs_repr],
  abs_map := λ α β f p, by rw [abs_map,FG_abs_map] }

end repr

section rel

variables (R : ∀ ⦃α⦄, F α → F α → Prop)

def quot1 (α : typevec n) :=
quot (@R α)

variables (Hfunc : ∀ ⦃α β⦄ (a b : F α) (f : α ⟹ β), R a b → R (f <$$> a) (f <$$> b))

def quot1.map ⦃α β⦄ (f : α ⟹ β) : quot1.{u} R α → quot1.{u} R β :=
quot.lift (λ x : F α, quot.mk _ (f <$$> x : F β)) $ λ a b h,
  quot.sound $ Hfunc a b _ h

instance : mvfunctor (quot1 R) :=
{ map := quot1.map R Hfunc  }

variables (Hrefl : ∀ ⦃α⦄ (a : F α), R a a)

noncomputable def rel_quot : @mvqpf _ (quot1 R) (mvqpf.mvfunctor R Hfunc) :=
@quotient_qpf n F _ q _ (mvqpf.mvfunctor R Hfunc) (λ α x, quot.mk _ x) (λ α, quot.out)
  (λ α x, quot.out_eq _)
  (λ α β f x, quot.sound (Hfunc _ _ _ (Hrefl _)))

end rel

end mvqpf
