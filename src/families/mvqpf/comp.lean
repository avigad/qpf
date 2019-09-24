
import families.mvpfunctor.basic
import families.mvqpf.basic

import category_theory.products

universes u

namespace mvqpf
variables {I J K : Type u}
  (F : fam I ⥤ fam J) [q  : mvqpf F]
  (G : fam J ⥤ fam K) [q' : mvqpf G]

open category_theory

-- def comp (v : fam J) : fam K :=
-- -- F $ λ i : fin' n, G i v
-- λ k : K, F.obj (λ i : I, (G i).obj v k) _

namespace comp
open mvfunctor mvpfunctor
variables {F G} {α β : fam J} (f : α ⟶ β)

-- protected def mk (x : F $ λ i, G i α) : (comp F G) α := x

-- protected def get (x : (comp F G) α) : F $ λ i, G i α := x

-- @[simp] protected lemma mk_get (x : (comp F G) α) : comp.mk (comp.get x) = x := rfl

-- @[simp] protected lemma get_mk (x : F $ λ i, G i α) : comp.get (comp.mk x) = x := rfl

-- protected def map' : (λ (i : fin' n), G i α) ⟹ λ (i : fin' n), G i β :=
-- λ i, map f

-- protected def map : (comp F G) α → (comp F G) β :=
-- (map (λ i, map f) : F (λ i, G i α) → F (λ i, G i β))

-- instance : mvfunctor (comp F G) :=
-- { map := λ α β, comp.map }

-- lemma map_mk (x : F $ λ i, G i α) :
--   f <$$> comp.mk x = comp.mk ((λ i (x : G i α), f <$$> x) <$$> x) := rfl

-- lemma get_map (x : comp F G α) :
--   comp.get (f <$$> x) = (λ i (x : G i α), f <$$> x) <$$> comp.get x := rfl

include q q'

local attribute [simp] category_theory.functor.map_comp_map category_theory.functor.map_comp_map_assoc
local attribute [-simp] functor.map_comp functor.map_comp_assoc

instance : mvqpf (F ⋙ G) :=
{ P         := pfunctor.comp (P G) (P F),
  abs       := λ α, pfunctor.comp.get _ _ α ≫ (P G).map (abs F _) ≫ abs G _ ≫ 𝟙 (G.obj (F.obj α)),
  repr      := λ α, 𝟙 (G.obj (F.obj α)) ≫ @repr _ _ G q' _ ≫ (P G).map (repr F α) ≫ pfunctor.comp.mk _ _ _,
  abs_repr := by { intros, simp [category_theory.category.id_comp], erw category_theory.category.id_comp, refl },
  abs_map  := by { intros, simp [abs_map], } }

end comp

end mvqpf
