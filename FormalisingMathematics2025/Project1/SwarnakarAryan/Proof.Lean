import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.ContinuousOn

open Function
open Real
open Set

/-!
# Rolle's Theorem in Lean

This file provides a formalization of a naive proof of Rolle's Theorem.

## Main Results
- `Rolle's Theorem`: The main theorem.
- `Fermat's Theorem`: A key statement in Rolle's Theorem.

## Definitions
- `ConstantFunction`: A function that takes equal values at every point in a given interval.
- `FermatesTheorem`: The formalization of Fermat's theorem.
- `isLocalMaximum` and `isLocalMinimum`: Definitions of local extrema in a closed interval.
- `ContinousOnClosedIntervalImpliesMaxExists` and `ContinousOnClosedIntervalImpliesMinExists`:
  Statements that ensure the existence of extrema in a continuous function over a closed interval.

## Dependencies
- Uses standard results from Lean's `Mathlib.Analysis.Calculus.Deriv.Basic` and
  `Mathlib.Topology.ContinuousOn`.
- Relies on the concept of compactness for proving extrema existence.

-/

/--
A continuous function on a closed interval `[a, b]` attains a **maximum** at some `c ∈ [a, b]`.
This follows from the compactness of `[a, b]`.
-/
theorem continuous_max_exists {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h_cont : ContinuousOn f (Icc a b)) :
    ∃ c : Icc a b, ∀ x ∈ Icc a b, f c ≥ f x := by -- we have nice unicode in Lean, use it!
  -- Proof `[a,b]` is compact
  have h_compact : IsCompact (Icc a b) := isCompact_Icc -- by exact cancel each other
  obtain ⟨c, hc, h_max⟩ := h_compact.exists_isMaxOn (nonempty_Icc.2 hab.le) h_cont -- nice
  -- you could condense this even more, if you want:
  -- obtain ⟨c, hc, h_max⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab.le) h_cont
  use ⟨c, hc⟩
  intro x hx
  exact h_max hx
  -- notice you didn't use a < b, only that a ≤ b
  -- also, note the output of this theorem is
  --     ∃ c : Icc a b, ∀ x ∈ Icc a b, f c ≥ f x
  -- which is technically different from
  --     ∃ c ∈ Icc a b, ∀ x ∈ Icc a b, f c ≥ f x
  -- You'll probably have found this a tiny bit easier if you used the latter
  -- They're mathematically the same, but the first one makes an element of a subtype, whereas the
  -- second makes an element of the reals and shows it's in a specific subset

-- nice docstring
/--
A continuous function on a closed interval `[a, b]` attains a **minimum** at some `c ∈ [a, b]`.
This follows from the compactness of `[a, b]`.
-/
theorem continuous_min_exists {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h_cont : ContinuousOn f (Icc a b)) :
    ∃ c : Icc a b, ∀ x ∈ Icc a b, f c <= f x := by
  -- Proof `[a,b]` is compact
  have h_compact : IsCompact (Icc a b) := by exact isCompact_Icc
  obtain ⟨c, hc, h_min⟩ := h_compact.exists_isMinOn (nonempty_Icc.2 hab.le) h_cont
  use ⟨c, hc⟩
  intro x hx
  exact h_min hx
  -- could do this by consiering -f, like we discussed

/--
A function `f` has a **local maximum** at `c ∈ (a, b)` if `f(x) ≤ f(c)` for all `x ∈ [a, b]`.
-/
def isLocalMaximum (f : ℝ → ℝ) (a b : ℝ) (c : Ioo a b): Prop := ∀ x ∈ Icc a b, f x <= f c

-- I like your attempts to follow the naming conventions; although you didn't quite land it
-- (you didn't lose marks for that; actually you got a few bonus marks for the nice attempt)
-- https://leanprover-community.github.io/contribute/naming.html
-- rule 2 would say isLocalMaximum should be IsLocalMaximum
-- then rule 5 says this theorem should be isLocalMaximum_def
-- rule 2 also says fermats_theorem should be FermatsTheorem (cf FermatLastTheorem in mathlib)
theorem islocalmaximum_def {f : ℝ → ℝ} {a b : ℝ} (c : Ioo a b) :
    isLocalMaximum f a b c ↔ ∀ x ∈ Icc a b, f x <= f c := by
  rfl

/--
A function `f` has a **local minimum** at `c ∈ (a, b)` if `f(x) ≥ f(c)` for all `x ∈ [a, b]`.
-/
def isLocalMinimum (f : ℝ → ℝ) (a b : ℝ) (c : Ioo a b): Prop := ∀ x ∈ Icc a b, f x >= f c

theorem islocalminimum_def (f : ℝ → ℝ) (a b : ℝ) (c : Ioo a b) :
    isLocalMinimum f a b c ↔ ∀ x ∈ Icc a b, f x >= f c := by
  rfl

/--
A function `f` is **constant** on `[a, b]` if `f(x) = f(y)` for all `x, y ∈ [a, b]`.
-/
def ConstantFunction (f : ℝ → ℝ) (a b : ℝ): Prop := ∀ x y : Icc a b, f x = f y

/--
Fermat’s Theorem: If `f` has a local extremum at `c ∈ (a, b)`, then `deriv f c = 0`.
-/
def fermats_theorem (f : ℝ → ℝ) {a b: ℝ} (c : Ioo a b) : Prop :=
  (isLocalMaximum f a b c ∨ isLocalMinimum f a b c) → deriv f c = 0

/--
If a function `f` has a local maximum or minimum at `c`, then `f' c = 0`. This proves Fermat's
Theorem.
-/
theorem proof_of_fermatsTheorem {f : ℝ → ℝ} {a b: ℝ} (c : Ioo a b) :
    fermats_theorem f c := by
  rw [fermats_theorem]
  intro h_extremum
  rcases h_extremum with hLocalMaximum | hLocalMinimum
  -- Proof of isLocalMaximum is equvilent to IsLocalMax
  · have hLocalMax : IsLocalMax f c := by
      rw [IsLocalMax, IsMaxFilter, eventually_nhds_iff]
      -- Prove Ioo a b is a valid interval for c to be a local maximum
      use (Ioo a b)
      constructor
      -- Proof it is a local maximum
      · intro y hy
        -- Applying defintion from about
        rw [isLocalMaximum] at hLocalMaximum
        specialize hLocalMaximum y
        apply hLocalMaximum
        exact mem_Icc_of_Ioo hy
      -- Proof Ioo a b is a open set
      · constructor
        · exact isOpen_Ioo
        · exact Subtype.coe_prop c
    -- application of inbuilt fermats theorem
    exact IsLocalMax.deriv_eq_zero hLocalMax
  -- Proof of isLocalMinimum is equvilent to IsLocalMin
  · have c : IsLocalMin f c := by
      rw [IsLocalMin]
      rw [IsMinFilter]
      rw [eventually_nhds_iff]
      -- Prove Ioo a b is a valid interval for c to be a local minimum
      use (Ioo a b)
      constructor
      -- Proof it is a local minimum
      · intro y hy
        rw [isLocalMinimum] at hLocalMinimum
        specialize hLocalMinimum y
        apply hLocalMinimum
        exact mem_Icc_of_Ioo hy
      -- Proof Ioo a b is a open set
      · constructor
        · exact isOpen_Ioo
        · exact Subtype.coe_prop c
    -- application of inbuilt fermats theorem
    exact IsLocalMin.deriv_eq_zero c

/--
The midpoint of a consatnt function on `[a,b]` has 0 derivative
-/
theorem deriv_eq_zero_of_const_midpoint (f : ℝ → ℝ) (a b : ℝ)
    (h_const : ConstantFunction f a b) (h_mid : (a + (b - a) / 2) ∈ Ioo a b) :
    deriv f ((a + (b - a) / 2)) = 0 := by
  -- Prove midpoint is a local maximum
  have h_local_max : isLocalMaximum f a b ⟨(a + (b - a) / 2), h_mid⟩ := by
    rw [isLocalMaximum]
    intro x hx
    rw [ConstantFunction] at h_const
    have h_midpoint_mem_Icc : a + (b - a) / 2 ∈ Icc a b := by
      exact mem_Icc_of_Ioo h_mid
    specialize h_const ⟨x, hx⟩ ⟨a + (b - a) / 2, h_midpoint_mem_Icc⟩
    rw [le_iff_lt_or_eq]
    right
    exact h_const
  -- All local maximums on continous functions have 0 derivatives
  refine IsLocalMax.deriv_eq_zero ?_
  -- Convert isLocalMaximum to IsLocalMax
  rw [IsLocalMax, IsMaxFilter, eventually_nhds_iff]
  use (Ioo a b)
  constructor
  · intro y hy
    rw [islocalmaximum_def] at h_local_max
    specialize h_local_max y
    apply h_local_max
    exact mem_Icc_of_Ioo hy
  · constructor
    · exact isOpen_Ioo
    · exact h_mid

/--
If `f` has both its maximum and minimum at endpoints of `[a, b]`, then `f` is constant on `[a, b]`.
-/
theorem constant_if_extrema_at_endpoints {f : ℝ → ℝ} {a b: ℝ} (max_pos min_pos : Icc a b)
    (h_max_ge_all : ∀ x : Icc a b, f max_pos ≥ f x) (h_min_le_all : ∀ x : Icc a b, f min_pos <= f x)
    (h_eq_endpoints : f a = f b)
    (h_max_at_endpoints : max_pos = a ∨ max_pos = b)
    (h_min_at_endpoints : min_pos = a ∨ min_pos = b) :
    ConstantFunction f a b := by
  rw [ConstantFunction]
  intro x y
  -- Goes through all the cases of where the min and max can lie
  have h_max_eq_min : f max_pos = f min_pos := by
    rcases h_max_at_endpoints with h_max_endpoint | h_max_endpoint
    · rcases h_min_at_endpoints with h_min_endpoint | h_min_endpoint <;>
      simp_all
    · rcases h_min_at_endpoints with h_min_endpoint | h_min_endpoint <;>
      simp_all
  -- Proof x equals the max value
  have h_x_eq_max : f x = f max_pos := by
    apply le_antisymm
    · exact h_max_ge_all x
    · specialize h_min_le_all x
      rw [h_max_eq_min]
      apply h_min_le_all
  -- Proof x equals the min value
  have h_y_eq_max : f y = f max_pos := by
    apply le_antisymm
    · exact h_max_ge_all y
    · specialize h_min_le_all y
      rw [h_max_eq_min]
      apply h_min_le_all
  -- Since x is the max and the min that means that must be equal so f is constant as x was arbitary
  rw [h_x_eq_max, h_y_eq_max]

/--
If a function `f` has a local maximum at `c ∈ (a, b)`, then its derivative at `c` is zero.
This follows directly from Fermat's theorem.
-/
theorem deriv_at_local_max (f : ℝ → ℝ) (a b : ℝ) (c : Ioo a b) (hMax : isLocalMaximum f a b c) :
    deriv f c = 0 := by
  have fermate_conditions : (isLocalMaximum f a b c) ∨ (isLocalMinimum f a b c) := Or.inl hMax
  exact proof_of_fermatsTheorem c fermate_conditions

/--
If a function `f` has a local minimum at `c ∈ (a, b)`, then its derivative at `c` is zero.
This is a direct application of Fermat's theorem.
-/
theorem deriv_at_local_min (f : ℝ → ℝ) (a b : ℝ) (c : Ioo a b) (hMin : isLocalMinimum f a b c) :
    deriv f c = 0 := by
  have fermate_conditions : (isLocalMaximum f a b c) ∨ (isLocalMinimum f a b c) := Or.inr hMin
  exact proof_of_fermatsTheorem c fermate_conditions

/--
Rolle’s Theorem: If `f` is continuous on `[a, b]`, differentiable on `(a, b)`, and `f(a) = f(b)`,
then there exists some `c ∈ (a, b)` such that `f' c = 0`.
-/
theorem rolles_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (h_cont : ContinuousOn f (Icc a b))
    (heq : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 := by
  -- Maximum on a continous function exists
  obtain ⟨⟨c_max, h_max_in_interval⟩, hc⟩ := continuous_max_exists hab h_cont
  -- Case 1 : Interiour Maximum
  by_cases h_max_interior : a < c_max ∧ b > c_max
  · have isMax : isLocalMaximum f a b ⟨c_max, by exact h_max_interior⟩ := by rwa [isLocalMaximum]
    use c_max
    constructor
    · exact h_max_interior
    · exact deriv_at_local_max f a b ⟨c_max, by exact h_max_interior⟩ isMax

  -- Minimum on a continous function exists
  obtain ⟨⟨c_min, h_min_in_interval⟩, hm⟩ := continuous_min_exists hab h_cont
  -- Case 2 : Interiour Minimum
  by_cases h_min_interior : a < c_min ∧ b > c_min
  · have isMin : isLocalMinimum f a b ⟨c_min, by exact h_min_interior⟩ := by rwa [isLocalMinimum]
    use c_min
    constructor
    · exact h_min_interior
    · exact deriv_at_local_min f a b ⟨c_min, by exact h_min_interior⟩ isMin

  -- Proof the maximum must lie at a or b
  have maxPosLocations : a = c_max ∨ b = c_max := by
    rw [not_and_or] at h_max_interior
    simp only [not_lt, gt_iff_lt] at h_max_interior
    -- max is either at a or b
    rcases h_max_interior with max_at_a|max_at_b
    · left
      apply le_antisymm
      · rw [mem_Icc] at h_max_in_interval
        exact h_max_in_interval.left
      · exact max_at_a
    · right
      apply le_antisymm
      · exact max_at_b
      · rw [mem_Icc] at h_max_in_interval
        exact h_max_in_interval.right

  -- Proof the minimum must lie at a or b
  have minPosLocations : a = c_min ∨ b = c_min := by
    rw [not_and_or] at h_min_interior
    simp only [not_lt, gt_iff_lt] at h_min_interior
    -- min is either at a or b
    rcases h_min_interior with min_at_a|min_at_b
    · left
      apply le_antisymm
      · rw [mem_Icc] at h_min_in_interval
        exact h_min_in_interval.left
      · exact min_at_a
    · right
      apply le_antisymm
      · exact min_at_b
      · rw [mem_Icc] at h_min_in_interval
        exact h_min_in_interval.right

  -- In the remaining case we must have the min and max are at the end points
  -- Thus f must be a constant function since f a = f b
  have h_f_constant : ConstantFunction f a b := by
    -- Go through all the cases of min and max assignment
    rcases minPosLocations with n | n <;>
    rcases maxPosLocations with m | m <;>
    exact constant_if_extrema_at_endpoints ⟨c_max, h_max_in_interval⟩
      ⟨c_min, h_min_in_interval⟩ (λ x ↦ hc x x.2) (λ x ↦ hm x x.2) heq (by aesop) (by aesop)

  -- Proof derivative at midpoint is 0
  use (a + (b - a) / 2)
  constructor
  · norm_num
    constructor
    · exact hab
    · linarith
  -- Proof midpoint is in the open set (a,b)
  · have middle_is_in_set : a + (b - a) / 2 ∈ Ioo a b := by
      norm_num
      constructor
      · exact hab
      · linarith
  -- Proof derivative at midpoint is 0
    exact deriv_eq_zero_of_const_midpoint f a b h_f_constant middle_is_in_set
