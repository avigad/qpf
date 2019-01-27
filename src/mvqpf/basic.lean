/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Multivariate quotients of polynomial functors.
-/
import ..mvpfunctor.W
universe u

class mvqpf {n : ℕ} (F : typevec.{u} n → Type*) [mvfunctor F] :=
(P         : mvpfunctor.{u} n)
(abs       : Π {α}, P.apply α → F α)
(repr'     : Π {α}, F α → P.apply α)
(abs_repr' : ∀ {α} (x : F α), abs (repr' x) = x)
(abs_map   : ∀ {α β} (f : α ⟹ β) (p : P.apply α), abs (f <$$> p) = f <$$> abs p)

namespace mvqpf
variables {n : ℕ} {F : typevec.{u} n → Type*} [mvfunctor F] [q : mvqpf F]
include q

def repr {α : typevec n} (x : F α) := repr' n x

theorem abs_repr {α : typevec n} (x : F α) : abs (repr x) = x :=
abs_repr' n x

attribute [simp] abs_repr

/- 
Show that every mvqpf is a lawful mvfunctor. 
-/

theorem id_map {α : typevec n} (x : F α) : typevec.id <$$> x = x :=
by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map], reflexivity }

theorem comp_map {α β γ : typevec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α) : 
  (g ⊚ f) <$$> x = g <$$> f <$$> x :=
by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map, ←abs_map, ←abs_map], reflexivity }

instance is_lawful_mvfunctor : is_lawful_mvfunctor F :=
{ mv_id_map := @id_map n F _ _,
  mv_comp_map := @comp_map n F _ _ }

end mvqpf
