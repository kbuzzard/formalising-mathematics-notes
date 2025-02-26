import Mathlib.Tactic
import Mathlib.Tactic
import Mathlib.Data.Setoid.Partition
/-
In this project I prove that the set of cosets {gH : g ∈ G] of a group G partition the group.
I do this with the following steps:
  ⬝ Prove that cosets are equal if they are not disjoint (with
    coset_subset_if_not_disjoint, and not_disjoint_implies_equal).
  ⬝ I then prove that cosets partition the group (cosets_partition_group) by proving that
    1) ∅ ∉ {gH : g ∈ G}
    2) Every element x ∈ G is contained in a unique coset (using not_disjoint_implies_equal)

Additionally I prove that gH = H for all g ∈ H, and that x ∈ xH for all x ∈ G.

My varible naming follows the convention shown in mem_coset_iff, that is:
  ⬝ I work with an arbitrary group G, and subgroup H.
  ⬝ I use k and h to denote elements in H.
  ⬝ I use g to dentote an arbitrary element in the group which has coset gH,
    with elements g * h ∀ h ∈ H.
  ⬝ I use x to be an arbitarary element of the group, which is often in a coset gH
    so that x = g * h for some h ∈ H.
-/

open Setoid
open Set

/-- The left coset gH of the subgroup H of G -/
def Group.coset {G : Type} [Group G] (H : Subgroup G) (g : G) : Set G :=
  {x : G | ∃ h ∈ H, x = g * h}

namespace Group

variable {G : Type} [Group G] (H : Subgroup G) (g : G) (x : G)

lemma mem_coset_iff : x ∈ coset H g ↔ ∃ h ∈ H, x = g * h := by
  rfl

lemma x_mem_xH (H : Subgroup G): x ∈ coset H x := by
  rw [mem_coset_iff]
  use 1
  aesop

example (h1 : g ∈ H) : coset H g = H := by
  ext x
  rw [mem_coset_iff]
  constructor
  · intro h2
    rcases h2 with ⟨y, hy, h_x_is_gy⟩
    have hx : x ∈ H := by
      rwa [h_x_is_gy, Subgroup.mul_mem_cancel_left H h1]
      -- make sure you understand what I did here!
    exact hx
  · intro hx
    have hg : g⁻¹ ∈ H := by rwa [inv_mem_iff]
    use (g⁻¹ * x)
    constructor
    · rwa [Subgroup.mul_mem_cancel_left H hg]
    · rw [mul_inv_cancel_left]


/-- Given a group G and subgroup H, if g₁H ∩ g₂H ≠ ∅, then g₁H ⊆ g₁H. -/
lemma coset_subset_if_not_disjoint (g₁ g₂ : G) (H : Subgroup G)
   (h_not_disjoint : coset H g₁ ∩ coset H g₂ ≠ ∅) :
    coset H g₁ ⊆ coset H g₂ := by
  rw [subset_def]
  -- lemmas with Tactic in their name like this aren't *meant* to be used
  -- but technically this is rw?'s fault for telling you about it, not yours
  -- rw [@Mathlib.Tactic.PushNeg.ne_empty_eq_nonempty] at h_not_disjoint
  rw [← Set.nonempty_iff_ne_empty] at h_not_disjoint

  -- We want to consider an arbitary x in the non-empty intersection
  have hx : ∃ x, x ∈ coset H g₁ ∧ x ∈ coset H g₂ := h_not_disjoint
  -- We will want to use the facts that x ∈ g₁H and x ∈ g₂H separately, so lets break up hx.
  -- Very sensible, but you can do that all at once
  rcases hx with ⟨x, h_x_mem_g₁H, h_x_mem_g₂H⟩
  -- in fact I can also combine the last two lines:
  -- have ⟨x, h_x_mem_g₁H, h_x_mem_g₂H⟩ : ∃ x, x ∈ coset H g₁ ∧ x ∈ coset H g₂ := h_not_disjoint

  -- The next step is to write x = g₁ * h₁ and x = g₂ * h₂ for some g₁, g₂ ∈ G, h₁, h₂ ∈ H.
  have h_x_eq_g₁h₁ : ∃ (h₁ : G), h₁ ∈ H ∧ x = g₁ * h₁ := by
    rw [mem_coset_iff] at h_x_mem_g₁H
    cases' h_x_mem_g₁H with h₁ h_h₁
    cases' h_h₁ with h_h₁ h_x_eq_g₁h₁
    use h₁
  have h_x_eq_g₂h₂ : ∃ (h₂ : G), h₂ ∈ H ∧ x = g₂ * h₂ := by
    rw [mem_coset_iff] at h_x_mem_g₂H
    cases' h_x_mem_g₂H with h₂ h_h₂
    cases' h_h₂ with h_h₂ h_x_eq_g₂h₂
    use h₂

  -- We want break down the ∃ h₁ and ∃ h₂ so that we can access them
  rcases h_x_eq_g₁h₁ with ⟨h₁, h_h₁_mem_H, h_x_eq_g₁h₁⟩
  -- BM: these combine!!
  -- same thing above and below
  -- rcases means recursive cases

  cases' h_x_eq_g₂h₂ with h₂ h_x_eq_g₂h₂
  cases' h_x_eq_g₂h₂ with h_h₂_mem_H h_x_eq_g₂h₂

  -- We now want to deduce that g₁ * h₁ = g₂ * h₂ and therefore g₁ = g₂ * h₂ * g₁⁻¹.
  have h_g₁h₁_eq_g₂h₂ : g₁ * h₁ = g₂ * h₂ := by
    rw [← h_x_eq_g₁h₁]
    exact h_x_eq_g₂h₂

  have h_g₁_eq_g₂h₂g₁_inv : g₁ = g₂ * h₂ * h₁⁻¹ := by
    rw [mul_inv_eq_of_eq_mul (Eq.symm h_g₁h₁_eq_g₂h₂)]

  -- We want to consider an arbitrary g₁k ∈ g₁H, and rewrite it as g₂ * (h₂ * h₁⁻¹ * k)
  -- Initially I use g₁ * k = (g₂ * h₂ * h₁⁻¹) * k and then change the bracketing:
  have h_rewrite (k : G) : k ∈ H → g₁ * k = g₂ * (h₂ * h₁⁻¹ * k) := by
    intro
    rw [h_g₁_eq_g₂h₂g₁_inv]
    -- Change bracketing
    group

  -- Our next step is to note that g₁ * k = g₂ * k' for k' = h₂ * h₁⁻¹ * k
  -- and that h₂ * h₁⁻¹ * k ∈ H.
  -- Therefore g₁ * k ∈ g₂H.
  have h_g₁k_in_g₂H (k : G): k ∈ H → g₁ * k ∈ coset H g₂ := by
    intro h_k_mem_H
    have h : h₂ * h₁⁻¹ * k ∈ H := by
      rw [Subgroup.mul_mem_cancel_right H h_k_mem_H, Subgroup.mul_mem_cancel_left H h_h₂_mem_H]
      simp -- nonterminal simp
      exact h_h₁_mem_H
      -- in this case you could have fixed it with simpa
      -- but in general simp? will tell you what to replace it with

    have h_exists_k' : ∃ k' ∈ H, g₁ * k = g₂ * k' := by
      use (h₂ * h₁⁻¹ * k)
      exact ⟨h, h_rewrite k h_k_mem_H⟩

    -- Breakdown h_exists_k'
    cases' h_exists_k' with k' temp
    cases' temp with h_kinH h_g₁k_eq_g₂k'

    -- Prove g₁ * k ∈ g₂H
    rw [h_g₁k_eq_g₂k']
    rw [mem_coset_iff]
    use k'

-- We now know that given an arbitrary x = g₁ * k ∈ g₁H,
-- that x ∈ g₂H. We just need to make this explicit.
  simp only [mem_coset_iff H g₁]
  -- We need the arbitrary x ∈ g₁H
  intro x
  -- We need the hypothesis that tells us that x ∈ g₁H
  intro h
  -- We need the hypothesis that tells us we can write x = g₁ * k
  cases' h with k temp
  cases' temp with h_k_mem_H h_x_eq_g₁k
  -- We know that x = g₁ * k ∈ g₁H → g₁ * k ∈ g₁H
  apply h_g₁k_in_g₂H at h_k_mem_H
  -- We apply the fact that x = g₁ * k to change the hypothesis
  rw [h_x_eq_g₁k]
  -- We know g₁ * y ∈ g₁H
  exact h_k_mem_H

/-- Given a group G and subgroup H, if g₁H ∩ g₂H ≠ ∅, then g₁H = g₁H. -/
theorem not_disjoint_implies_equal (g₁ g₂: G) (H : Subgroup G) :
    coset H g₁ ∩ coset H g₂ ≠ ∅ → coset H g₁ = coset H g₂ := by
  intro h_not_disjoint
  -- We split up the '=' into two subset statements as always
  rw [Subset.antisymm_iff]
  constructor
  · exact coset_subset_if_not_disjoint g₁ g₂ H h_not_disjoint
  · rw [inter_comm] at h_not_disjoint
    exact coset_subset_if_not_disjoint g₂ g₁ H h_not_disjoint


/-- Given a group G and subgroup H, the set of cosets {gH : g ∈ G} partition the group -/
theorem cosets_partition_group : IsPartition {S : Set G | ∃ g, S = coset H g} := by
  /-
  I need to show that:
   1) ∅ ∉ {gH : g ∈ G}
   2) ∀ x ∈ G, ∃! S ∈ {gH : g ∈ G}, x ∈ S
  -/
  -- I will first prove 1
  -- good comments
  have emptyset_not_mem : ∅ ∉ {S : Set G | ∃ g, S = coset H g} := by
    simp only [mem_setOf_eq, not_exists]
    intro x
    have h_x_mem_xH : x ∈ coset H x := x_mem_xH x H
    -- Assume that xH = ∅
    by_contra h
    -- x ∈ xH so x ∈ ∅
    rw [← h] at h_x_mem_xH
    -- This is false by definition
    exact h_x_mem_xH

  -- I will prove 2 using the previous lemma
  have mem_unique_coset : ∀ (x : G), ∃! X ∈ {S : Set G | ∃ g, S = coset H g}, x ∈ X := by
    intro x
    -- We know x ∈ xH, we will use this twice in this proof
    have h_x_mem_xH : x ∈ coset H x := x_mem_xH x H
    use coset H x
    simp
    constructor
    · exact h_x_mem_xH
    · intro g
      -- Suppose x ∈ kH
      intro h_x_in_gH
      -- We know kH and xH both contain x
      have not_disjoint : coset H x ∩ coset H g ≠ ∅ := by
        rw [@Mathlib.Tactic.PushNeg.ne_empty_eq_nonempty]
        rw [@inter_nonempty_iff_exists_right]
        use x
      -- Use the main lemma from before
      apply not_disjoint_implies_equal g x H
      rw [@inter_comm]
      exact not_disjoint

  -- We now have exactly the ingredients for IsPartition
  exact ⟨emptyset_not_mem, mem_unique_coset⟩
