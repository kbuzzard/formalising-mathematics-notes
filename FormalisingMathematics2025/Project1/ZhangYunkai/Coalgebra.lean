/-
Copyright (c) 2025 Yunkai Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunkai Zhang
-/
import Mathlib.Tactic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Lambek's Lemma, Dual Form

This file formalises the dual form of Lambek's Lemma for coalgebras.

Lambek's Lemma's dual form states that for an endofunctor `F`,
If an F-coalgebra is terminal,
then its structural map is an isomorphism.

The proof follows categorical axioms, demonstrating the existence of inverse morphisms
using the universal properties of terminal objects.

## Main declarations

* `FCoalgebra`: Structure for an F-coalgebra with carrier object and structural morphism
* `CoalgebraHom`: The homomorphisms between F-coalgebras
* `FCoalgebra.Terminal.lambek_co`: The dual form of lambek's lemma for terminal F-coalgebras

## Implementation notes

The implementation builds upon mathlib's category theory foundations, particularly using:
* Category type classes and structures
* Terminal object definitions from limits
* Isomorphism type classes

We define the category of FF-coalgebras by providing appropriate morphism structures
and proving the categorical axioms.

## References

* [S. Awodey, *Category Theory*][awodey2010]
* [nLab, *Terminal Coalgebra for an Endofunctor*][nlab]
* [A. Kissinger and J. Rot, *Colecture 1: Algebras, algebraic data types, and recursion*][kissinger2016]
-/


set_option autoImplicit false

namespace CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

local notation:80 g " ⊚ " f:80 => CategoryTheory.CategoryStruct.comp f g

variable {F : C ⥤ C}

structure FCoalgebra (F : C ⥤ C) where
  /-- carrier -/
  carrier : C
  /-- the arrow -/
  mor : carrier ⟶ F.obj carrier

namespace FCoalgebra


/-- Define that all F-Coalgebra form a category.
This include components:
* homomorphisms: `h : (A, α) ⟶ (B, β)` is essentially an arrow `h : A ⟶ B`
  such that `F (h) ∘ α = β ∘ h`
* identities: identity arrows

```
         F h
   F A -----> F B
    ∧         ∧
  α |         | β
    |         |
    A  -----> B
        h
```
-/

@[ext]
structure CoalgebraHom (A B : FCoalgebra F) where
  -- mathching carrier
  h : A.carrier ⟶ B.carrier
  -- commute condition
  condition : (F.map h) ⊚ A.mor = B.mor ⊚ h

variable (A : FCoalgebra F){A' B' C': FCoalgebra F}

/-
  Similarly we define the categorical structure stuff for coalgebras
-/


namespace CoalgebraHom

def id : CoalgebraHom A A where
  h := 𝟙 _
  condition := by
    aesop

-- Composition of homomorphisms between algebras
def comp (m1: CoalgebraHom A' B') (m2: CoalgebraHom B' C') : CoalgebraHom A' C' where
  h := m2.h ⊚ m1.h
  condition := by
    simp [Functor.map_comp]
    rw [← m2.condition]
    simp [← Category.assoc]
    rw [m1.condition]

end CoalgebraHom

instance (F : C ⥤ C) : CategoryStruct (FCoalgebra F) where
  Hom := CoalgebraHom
  id := CoalgebraHom.id -- (X : FAlgebra F) → X ⟶ X
  comp := @CoalgebraHom.comp _ _ _ -- {X Y Z : FAlgebra F} → (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

@[ext]
lemma ext {A B : FCoalgebra F} {f g : A ⟶ B} (w : f.h = g.h) : f = g :=
  CoalgebraHom.ext w

theorem comp_distr {f : B' ⟶ C'}{g : A' ⟶ B'} : (f ⊚ g).h = f.h ⊚ g.h := by
  rfl

theorem id_distr {A : FCoalgebra F}: (𝟙 _ : A ⟶ A).h = 𝟙 A.carrier := by
  rfl


-- We need to show: All F-Coalgebras form a category
instance (F : C ⥤ C) : Category (FCoalgebra F) := {
  --  ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f
  id_comp := by
    intros X Y f
    ext
    rw [comp_distr, id_distr, Category.id_comp]
  -- ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f
  comp_id := by
    intros X Y f
    ext
    rw [comp_distr, id_distr, Category.comp_id]
  -- Composition in a category is associative.
  assoc := by
    intros W X Y Z f g h
    ext
    simp [comp_distr]
}

/- The co-structure of the proof for that of the initial algebra -/
namespace Terminal
  -- terminal coalgebra
variable {T : FCoalgebra F}

abbrev ft_to_t (hTerminal : Limits.IsTerminal T) :=
  (hTerminal.from ⟨F.obj T.carrier, F.map T.mor⟩)


/-
  Construct the homomorphism from Algebra (I, i) to (I, i),
  which is formed by composing the homomorphism from (I, i) to (F(I), F(i))
  and the homomorphism from (F(I), F(i)) to (I, i)
-/
def t_to_t_coalg_hom (hTerminal : @Limits.IsTerminal (FCoalgebra F) _ T) : T ⟶ T where
  h :=  (ft_to_t hTerminal).h ⊚ T.mor
  condition:= by
    rw [Category.assoc, F.map_comp, ft_to_t, ← CoalgebraHom.condition]

/- f ⊚ t = id_T -/
lemma is_inv_1 (hTerminal : @Limits.IsTerminal (FCoalgebra F) _ T) :
    (ft_to_t hTerminal).h ⊚ T.mor = 𝟙 T.carrier := by
  have h1 : t_to_t_coalg_hom hTerminal = 𝟙 T :=
    Limits.IsTerminal.hom_ext hTerminal _ (𝟙 T)
  have h2 : (t_to_t_coalg_hom hTerminal).h = 𝟙 T.carrier :=
    congr_arg CoalgebraHom.h h1
  rw [← h2]
  unfold t_to_t_coalg_hom
  simp

/- t ⊚ f = id_F(T) -/
lemma is_inv_2 (hTerminal : @Limits.IsTerminal (FCoalgebra F) _ T) :
    T.mor ⊚ (ft_to_t hTerminal).h  = 𝟙 (F.obj T.carrier) := by
  unfold ft_to_t
  rw [← (ft_to_t hTerminal).condition, ← F.map_id, ← F.map_comp]
  congr
  apply is_inv_1 hTerminal

theorem lambek_co (hTerminal : @Limits.IsTerminal (FCoalgebra F) _ T) : IsIso T.mor := {
  out := ⟨ (ft_to_t hTerminal).h, is_inv_1 hTerminal, is_inv_2 hTerminal  ⟩
}

end Terminal

end FCoalgebra

end CategoryTheory
