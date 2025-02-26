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

variable (A : FAlgebra F) {A' B' C': FAlgebra F}


namespace AlgebraHom

def id : AlgebraHom A A where
  h := 𝟙 _
  condition := by
    aesop

-- this is for proof 2 in the next def
attribute [reassoc] AlgebraHom.condition

-- Composition of homomorphisms between algebras
-- BM: this one needs a docstring
-- notation is /-- docstring -/
def comp (m1: AlgebraHom A' B') (m2: AlgebraHom B' C') : AlgebraHom A' C' where
  h := m2.h ⊚ m1.h
  condition := by
    -- original
    -- simp [Functor.map_comp]
    -- rw [← m2.condition]
    -- simp [← Category.assoc]
    -- rw [m1.condition]
    -- this has a nonterminal simp!

    -- proof 1
    -- rw [F.map_comp, Category.assoc, ← m2.condition, ← Category.assoc, m1.condition,
    --   Category.assoc]
    -- you can do this just with rewrites

    -- proof 2
    simp only [Functor.map_comp, Category.assoc]
    rw [← m2.condition, m1.condition_assoc]
    -- any lemma tagged with reassoc will generate an "associated" version
    -- that means a lemma f ⊚ g = h will get a new version which is
    -- f ⊚ (g ⊚ p) = h ⊚ p
    -- and call it "{original_name}_assoc"
    -- the idea is that simp will turn a chain of compositions into something of shape
    -- a ⊚ (b ⊚ (c ⊚ ...)), and so in f ⊚ (g ⊚ p) the original f ⊚ g = ... lemma won't match
    -- but the _assoc lemma will match
    -- making and using _assoc lemmas should mean you never need to do rw [← assoc]

end AlgebraHom

instance (F : C ⥤ C) : CategoryStruct (FAlgebra F) where
  Hom := AlgebraHom
  id := AlgebraHom.id -- (X : FAlgebra F) → X ⟶ X
  comp := @AlgebraHom.comp _ _ _ -- {X Y Z : FAlgebra F} → (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

@[ext]
lemma ext {A B : FAlgebra F} {f g : A ⟶ B} (w : f.h = g.h) : f = g :=
  AlgebraHom.ext w

theorem comp_distr {f : B' ⟶ C'} {g : A' ⟶ B'} : (f ⊚ g).h = f.h ⊚ g.h := by
  rfl

theorem id_distr {A : FAlgebra F}: (𝟙 _ : A ⟶ A).h = 𝟙 A.carrier := by
  rfl


-- We need to show: All F-Algebras form a category
instance (F : C ⥤ C) : Category (FAlgebra F) where
  -- use `where` rather than `:= {}`
  -- (some of the example sheets got this wrong, my bad!)
  --  ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f
  -- you can put `∀ x,` arguments before the `:=`
  -- but if they were `∀ {x},` then it doesn't like that
  -- so use {X Y f} and it's fine again
  id_comp {X Y} f := by
    ext
    rw [comp_distr, id_distr, Category.id_comp]
  -- ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f
  comp_id {X Y} f := by
    ext
    rw [comp_distr, id_distr, Category.comp_id]
  -- Composition in a category is associative.
  assoc {W X Y Z} f g h := by
    ext
    simp [comp_distr]

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
Given `I` is an initial object in the category of algebras on endofunctors:

BM: I'm being pedantic here, but whatever.
Initial objects / terminal objects are unique up to unique isomorphism, but they're not actually
unique! eg in the category of sets, {1} and {2} aren't the same object. They're isomorphic, and
there's a unique isomorphism between them, but they're not equal.
This remains true in Lean category theory

`f` is the unique arrow from Algebra of (F I --i--> I)
to Algebra of (F (F I) --F (i)--> F I)

so `i ⊚ f` constitutes an arrow from I to I.

However, by I being an initial object, there is one unique arrow from I to I,
which is the identity arrow. Therefore, `i ⊚ f = id_I`

With this in mind, as the left square commutes: we have

```
f ⊚ i = F (i) ⊚ F (f)
      = F (i ⊚ f)
      = F (id_I)
      = id_(F (I))
```

-/
namespace Initial

variable {I : FAlgebra F} -- The initial object
-- If I do
-- #where
-- (with your version, at this point in the file) then Lean tells me that it has no idea what the
-- type of `I` should be -- but presumably you want it to be the object in FAlgebra F which you're
-- gonna say later is initial
-- so be explicit about this

-- docstring notation again
/--
The initial algebra.
`abbrev` is used instead of `def` to make it possible to be unfolded
-/
abbrev i_to_fi (hInit : Limits.IsInitial I) :=
  hInit.to ⟨F.obj I.carrier, F.map I.mor⟩
-- giving the type of I explicitly means I don't need the @ in hInit

-- it might have been sensible to make the object
-- fi : FAlgebra F := ⟨F.obj I.carrier, F.map I.mor⟩
-- then this would just be `hInit.to fi`

/--
Construct the homomorphism from Algebra (I, i) to (I, i),
which is formed by composing the homomorphism from (I, i) to (F(I), F(i))
and the homomorphism from (F(I), F(i)) to (I, i)
-/
@[simps] -- this is making a lemma called i_to_i_alg_hom_h proved by rfl and marking it simp
-- change it to simps? to see it
def i_to_i_alg_hom (hInit : Limits.IsInitial I) : I ⟶ I where
  h := I.mor ⊚ (i_to_fi hInit).h
  condition := by
    rw [← Category.assoc, F.map_comp, i_to_fi, ← AlgebraHom.condition]

/- i ⊚ f = id_I -/
lemma is_inv_1 (hInit : Limits.IsInitial I) :
    I.mor ⊚ (i_to_fi hInit).h = 𝟙 I.carrier := by
  have h1 : i_to_i_alg_hom hInit = 𝟙 I := hInit.hom_ext _ (𝟙 I)
  have h2 : (i_to_i_alg_hom hInit).h = 𝟙 I.carrier :=
    congr_arg AlgebraHom.h h1
    -- another (weirder looking) option is
    -- congr(($h1).h)
    -- or
    -- congr(AlgebraHom.h ($h1))
  rw [← h2]
  simp -- this works because of the @[simps] I added to `i_to_i_alg_hom`
  -- more broadly, `unfold` is often a sign you have a missing rfl lemma

/-- f ⊚ I = id_F(I) -/
lemma is_inv_2 (hInit : @Limits.IsInitial (FAlgebra F) _ I) :
    (i_to_fi hInit).h ⊚ I.mor = 𝟙 (F.obj I.carrier) := by
  -- unfold i_to_fi
  -- not needed!
  rw [(i_to_fi hInit).condition, ← F.map_id, ← F.map_comp]
  congr
  apply is_inv_1 hInit

/--
Lambek's Lemma:
if Algebra I : F (i) --i--> I is an initial F-algebra,
Then i is an isomorphism, with F (I) ≅ I
-/
theorem lambek (hInit : @Limits.IsInitial (FAlgebra F) _ I) : IsIso I.mor where
  out := ⟨ (i_to_fi hInit).h, is_inv_2 hInit , is_inv_1 hInit ⟩

-- BM: I stopped here
-- just dualise the above comments for FCoalgebra :)
end Initial

end FAlgebra
