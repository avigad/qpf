
import mvpfunctor.basic
import mvqpf.basic

universes u

namespace mvqpf
variables {n m : ℕ}
  (F : typevec.{u} n → Type*) [mvfunctor F] [q : mvqpf F]
  (G : fin' n → typevec.{u} m → Type u) [∀ i, mvfunctor $ G i] [q' : ∀ i, mvqpf $ G i]

def comp (v : typevec.{u} m) : Type* :=
F $ λ i : fin' n, G i v

namespace comp
open mvfunctor mvpfunctor
variables {F G} {α β : typevec.{u} m} (f : α ⟹ β)

protected def mk (x : F $ λ i, G i α) : (comp F G) α := x

protected def get (x : (comp F G) α) : F $ λ i, G i α := x

@[simp] protected lemma mk_get (x : (comp F G) α) : comp.mk (comp.get x) = x := rfl

@[simp] protected lemma get_mk (x : F $ λ i, G i α) : comp.get (comp.mk x) = x := rfl

protected def map' : (λ (i : fin' n), G i α) ⟹ λ (i : fin' n), G i β :=
λ i, map f

protected def map : (comp F G) α → (comp F G) β :=
(map (λ i, map f) : F (λ i, G i α) → F (λ i, G i β))

instance : mvfunctor (comp F G) :=
{ map := λ α β, comp.map }

lemma map_mk (x : F $ λ i, G i α) :
  f <$$> comp.mk x = comp.mk ((λ i (x : G i α), f <$$> x) <$$> x) := rfl

lemma get_map (x : comp F G α) :
  comp.get (f <$$> x) = (λ i (x : G i α), f <$$> x) <$$> comp.get x := rfl

include q q'

instance : mvqpf (comp F G) :=
{ P         := mvpfunctor.comp (P F) (λ i, P $ G i),
  abs       := λ α, comp.mk ∘ map (λ i, abs) ∘ abs ∘ mvpfunctor.comp.get,
  repr      := λ α,  mvpfunctor.comp.mk ∘ repr ∘
                 map (λ i, (repr : G i α → (λ (i : fin' n), apply (P (G i)) α) i)) ∘ comp.get,
  abs_repr  := by { intros, simp [(∘), mvfunctor.map_map, (⊚), abs_repr] },
  abs_map   := by { intros, simp [(∘)], rw [← abs_map],
                    simp [mvfunctor.id_map, (⊚), map_mk, mvpfunctor.comp.get_map, abs_map,
                      mvfunctor.map_map, abs_repr] } }

end comp

end mvqpf
