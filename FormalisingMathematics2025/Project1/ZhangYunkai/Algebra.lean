/-
Copyright (c) 2025 Yunkai Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunkai Zhang
-/
import Mathlib.Tactic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Lambek's Lemma

This file formalises Lambek's Lemma.

Lambek's Lemma states that for an endofunctor `F`, if an F-algebra is initial,
then its structural map is an isomorphism.

The proof follows categorical axioms, demonstrating the existence of inverse morphisms
using the universal properties of initial/terminal objects.

## Main declarations

* `FAlgebra`: Structure for an F-algebra with carrier object and structural morphism
* `AlgebraHom`: The homomorphisms between F-algebras
* `FAlgebra.Initial.lambek`: The main theorem stating that initial F-algebras have isomorphic structural maps

## Implementation notes

The implementation builds upon mathlib's category theory foundations, particularly using:
* Category type classes and structures
* Initial object definitions from limits
* Isomorphism type classes

We define the category of F-algebras by providing appropriate morphism structures
and proving the categorical axioms.

## References

* [S. Awodey, *Category Theory*][awodey2010]
* [nLab, *Initial Algebra of an Endofunctor*][nlab]
* [A. Kissinger and J. Rot, *Colecture 1: Algebras, algebraic data types, and recursion*][kissinger2016]
-/

set_option autoImplicit false

namespace CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

-- following the conventional notation
local notation:80 g " ⊚ " f:80 => CategoryTheory.CategoryStruct.comp f g

variable {F : C ⥤ C}

structure FAlgebra (F : C ⥤ C) where
  /-- carrier -/
  carrier : C
  /-- the arrow for the structural morphism -/
  mor : F.obj carrier ⟶ carrier

namespace FAlgebra

/-- Define that all F-Algebra form a category.
This include components:
* homomorphisms: `h : (A, α) ⟶ (B, β)` is essentially an arrow `h : A ⟶ B`
  such that `h ∘ α = β ∘ F (h)`
* identities: identity arrows

```
         F h
   F A -----> F B
    |         |
  α |         | β
    V         V
    A  -----> B
        h
```
-/

@[ext]
structure AlgebraHom (A B : FAlgebra F) where
  -- mathching carrier
  h : A.carrier ⟶ B.carrier
  -- commutative conidition
  condition : h ⊚ A.mor = B.mor ⊚ (F.map h)

variable (A : FAlgebra F){A' B' C': FAlgebra F}


namespace AlgebraHom

def id : AlgebraHom A A where
  h := 𝟙 _
  condition := by
    aesop

-- Composition of homomorphisms between algebras
def comp (m1: AlgebraHom A' B') (m2: AlgebraHom B' C') : AlgebraHom A' C' where
  h := m2.h ⊚ m1.h
  condition := by
    simp [Functor.map_comp]
    rw [← m2.condition]
    simp [← Category.assoc]
    rw [m1.condition]

end AlgebraHom

instance (F : C ⥤ C) : CategoryStruct (FAlgebra F) where
  Hom := AlgebraHom
  id := AlgebraHom.id -- (X : FAlgebra F) → X ⟶ X
  comp := @AlgebraHom.comp _ _ _ -- {X Y Z : FAlgebra F} → (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)
--

@[ext]
lemma ext {A B : FAlgebra F} {f g : A ⟶ B} (w : f.h = g.h) : f = g :=
  AlgebraHom.ext w

theorem comp_distr {f : B' ⟶ C'}{g : A' ⟶ B'} : (f ⊚ g).h = f.h ⊚ g.h := by
  rfl

theorem id_distr {A : FAlgebra F}: (𝟙 _ : A ⟶ A).h = 𝟙 A.carrier := by
  rfl


-- We need to show: All F-Algebras form a category
instance (F : C ⥤ C) : Category (FAlgebra F) := {
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


/-
  The idea of the proof:

  ```
         F f           F (i)
   F I -----> F (F I) -------> F (I)
    |         |                 |
  i |         | F(i)            | i
    V         V                 V
    I  -----> F I ------------> I
        f             i
```
Given `I` is the initial object in the category of algebras on endofunctors:

`f` is the unique arrow from Algebra of (F I --i--> I)
to Algebra of (F (F I) --F (i)--> F I)

so `i ⊚ f` constitutes an arrow from I to I.

However, by I being the initial object, there is one unique arrow from I to I,
which is the identity arrow. Therefore, `i ⊚ f = id_I`

With this in mind, as the left swuare commutes: we have

```
f ⊚ i = F (i) ⊚ F (f)
      = F (i ⊚ f)
      = F (id_I)
      = id_(F (I))
```

-/
namespace Initial

variable {I} -- The initial object

/-
  The initial algebra.
  `abbrev` is used instead of `def` to make it possible to be unfolded
-/
abbrev i_to_fi (hInit : @Limits.IsInitial (FAlgebra F) _ I) :=
  (hInit.to ⟨F.obj I.carrier, F.map I.mor⟩)

/-
  Construct the homomorphism from Algebra (I, i) to (I, i),
  which is formed by composing the homomorphism from (I, i) to (F(I), F(i))
  and the homomorphism from (F(I), F(i)) to (I, i)
-/
def i_to_i_alg_hom (hInit : @Limits.IsInitial (FAlgebra F) _ I) : I ⟶ I where
  h := I.mor ⊚ (i_to_fi hInit).h
  condition:= by
    rw [← Category.assoc, F.map_comp, i_to_fi, ← AlgebraHom.condition]

/- i ⊚ f = id_I -/
lemma is_inv_1 (hInit : @Limits.IsInitial (FAlgebra F) _ I) :
    I.mor ⊚ (i_to_fi hInit).h = 𝟙 I.carrier := by
  have h1 : i_to_i_alg_hom hInit = 𝟙 I :=
    Limits.IsInitial.hom_ext hInit _ (𝟙 I)
  have h2 : (i_to_i_alg_hom hInit).h = 𝟙 I.carrier :=
    congr_arg AlgebraHom.h h1
  rw [← h2]
  unfold i_to_i_alg_hom
  simp

/- f ⊚ I = id_F(I) -/
lemma is_inv_2 (hInit : @Limits.IsInitial (FAlgebra F) _ I) :
    (i_to_fi hInit).h ⊚ I.mor = 𝟙 (F.obj I.carrier) := by
  unfold i_to_fi
  rw [(i_to_fi hInit).condition, ← F.map_id, ← F.map_comp]
  congr
  apply is_inv_1 hInit

/-
  Lambek's Lemma:
  if Algebra I : F (i) --i--> I is an initial F-algebra,
  Then i is an isomorphism, with F (I) ≅ I
-/
theorem lambek (hInit : @Limits.IsInitial (FAlgebra F) _ I) : IsIso I.mor := {
  out := ⟨ (i_to_fi hInit).h, is_inv_2 hInit , is_inv_1 hInit ⟩
}

end Initial

end FAlgebra
