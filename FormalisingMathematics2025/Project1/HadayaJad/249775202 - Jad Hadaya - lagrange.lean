/-
In this project, I will attempt to prove Lagrange's Theorem which
states that the order of a finite group is divisible by the order of
any of its subgroups
-/

import Mathlib.Tactic -- imports all the tactics

set_option autoImplicit true
-- in your next project, make sure this is *off* at the beginning of the file
-- see the announcement

/-
I will start by creating an instance of a group G and a subgroup H of G
(When I got to the point of proving that cosets have the same size, I came
back here to make the group and subgroup finite for simplicity.
I'm not 100% sure if Fintype is the right way to do it)
-/


variable (G : Type) [Group G] [Fintype G]
variable (H : Subgroup G) [Fintype H]

/-
I will then attempt to define the concept of a coset (I will stick with left
multiplicative cosets for now to keep things simple)
-/

def left_Coset (g : G) : Set G := { x | ∃ h ∈ H, g * h = x }

-- Some useful lemmas from the exercise sheets
lemma mem_def (X : Type) (P : X → Prop) (a : X) :
    a ∈ {x : X | P x} ↔ P a := by
  rfl

lemma mem_inter_iff (A : Set R) (B : Set R): x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
  Iff.rfl

-- Another useful lemma about equality of sets
lemma set_eq_def (X : Type) (A B : Set X) : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B := by
  rw [Set.ext_iff]


-- This simple lemma will prove that any element g of G is in the coset gH of H
lemma mem_self_coset (g : G) : g ∈ left_Coset G H g := by
  rw [left_Coset, mem_def]
  use 1
  simp [H.one_mem]


-- I will then prove a couple of lemmas about equality of cosets

lemma coset_eq_def1 (x y : G) : left_Coset G H x = left_Coset G H y ↔ y ∈ left_Coset G H x := by
  -- rw [set_eq_def]
  constructor
  · intro h₁
    rw [h₁]
    exact mem_self_coset G H y
  · rw [set_eq_def]
    intro h₁ z
    constructor
    · intro h₂
      rw [left_Coset, mem_def] at h₁ h₂ ⊢
      rcases h₁ with ⟨r₁, h₁, h₅⟩
      rcases h₂ with ⟨r₂, h₂, h₆⟩
      rw [← h₅]
      use r₁⁻¹ * r₂
      constructor
      -- Used rw? and exact? to get the two lines below
      · rw [Subgroup.mul_mem_cancel_right H h₂]
        exact (Subgroup.inv_mem_iff H).mpr h₁
      · rw [mul_assoc, ← mul_assoc r₁, mul_inv_cancel, one_mul, h₆]
    · intro h₂
      rw [left_Coset, mem_def] at h₁ h₂ ⊢
      rcases h₁ with ⟨r, h₁, h₃⟩
      rcases h₂ with ⟨r₂, h₂, h₄⟩
      use r * r₂
      constructor
      -- Line below achieved by using exact?
      · exact H.mul_mem h₁ h₂
      · rw [← mul_assoc, h₃, h₄]



lemma coset_eq_def2 (x y : G) : left_Coset G H x = left_Coset G H y ↔ x⁻¹ * y ∈ H := by
  constructor
  · intro h₁
    have h₂ : y ∈ left_Coset G H x := by
      rw [h₁]
      exact mem_self_coset G H y
    rw [left_Coset, mem_def] at h₂
    rcases h₂ with ⟨h, h₂, h₃⟩
    rw [← h₃, ←mul_assoc, inv_mul_cancel, one_mul]
    exact h₂
  · intro h₁
    have h₂ : y ∈ left_Coset G H x := by
      rw [left_Coset, mem_def]
      use x⁻¹ * y
      refine ⟨h₁, ?_⟩
      rw [←mul_assoc, mul_inv_cancel, one_mul]
    rw [coset_eq_def1]
    exact h₂


-- I will then attempt to prove some more lemmas that I will need to prove Lagrange's Theorem

def disjoint (A B : Set G) : Prop := A ∩ B = ∅

-- The first is that cosets are either equal or disjoint

lemma cosets_eq_or_dj (g h : G) :
    left_Coset G H g = left_Coset G H h ∨ disjoint G (left_Coset G H g) (left_Coset G H h) := by
  by_cases h₁ : h ∈ left_Coset G H g
  · left
    rwa [coset_eq_def1]
  · right
    rw [disjoint]
    ext x
    constructor
    · intro h₂
      rw [mem_inter_iff] at h₂
      cases' h₂ with h₂ h₃
      -- BM: at this point I can use coset_eq_def1 to finish early
      rw [← coset_eq_def1] at h₁ h₂ h₃
      apply h₁
      rw [h₂, ← h₃]
    · intro h₁
      cases' h₁

-- The second is that the cosets partition the group

lemma cosets_partition : (⋃ g : G, left_Coset G H g) = Set.univ := by
  ext x
  constructor
  · intro h
    -- I got the following line using exact? but I'm not sure if it's correct
    -- BM: it's correct because Lean accepts it!
    exact Set.mem_univ x
  · intro h
    -- I also got the line below using rw?
    rw [Set.mem_iUnion]
    use x
    exact mem_self_coset G H x

/-
The third is that all cosets are the same size, but to do that I will first define a
bijection between the subgroup and the coset. I really struggled with defining a function
that goes from the subgroup to the coset, so I couldn't carry on with the proof.
I have left all the code I wrote below commented out.
-/

open Function

-- All the below gave me type mismatch errors
-- def φ (h : H) (g : G) : Set G := g * h,
-- def φ (g : G) : H → left_Coset G H g := fun h ↦ g * h

-- I then tried to create a Set G instance of H, but this also caused some errors
def H' : Set G := H
def φ (g : G) : H' → Set G := fun h ↦ g * h

/-
Thus, even then trying to prove that this map is bijective was unsuccessful due to the errors
I got above, but I've kept my proof outline below
-/

lemma φ_bijective (H' : Set G) [Group G]: Bijective φ := by
  rw[Bijective]
  constructor
  · sorry
  · sorry

-- An alternative way to prove Lagrange's Theorem is to define the index of a subgroup in two different ways and prove that they are equal

-- The first way is to define the index as the order of the group divided by the order of the subgroup

def index (G: Type) [Group G] [Fintype G] (H: Subgroup G) [Fintype H] : ℕ := Fintype.card G / Fintype.card H

-- The second way  is to define the index as the number of cosets of the subgroup in the group, but I didn'nt know how to define the number of cosets

def index' (G: Type) [Group G] [Fintype G] (H: Subgroup G) [Fintype H] : ℕ := sorry

-- I could not complete the proof as I needed the bijection or index definitions above to prove that the cosets are the same size

theorem lagrange_theorem : Fintype.card G % Fintype.card H = 0 := by
  sorry

theorem lagrange_theorem' : index G H = index' G H := by
  sorry
