/-
Formalizing Mathematics 2025, Project 1:
Proving that a uniformly continuous function on two intervals with exactly one shared element is uniformly continuous on the union of the intervals in Lean 4.
Author: Jeff Lee
-/
import Mathlib.Tactic -- import all the tactics

-- First, we define open and half-open intervals in ℝ
/-- Equivalent to (a, b) ⊆ ℝ -/
def open_interval (a b : ℝ) : Set ℝ := {x : ℝ | a < x ∧ x < b}
/-- Equivalent to [a, b) ⊆ ℝ -/
def half_open_interval_right (a b : ℝ) : Set ℝ := {x : ℝ | a ≤ x ∧ x < b}
/--Equivalent to (a, b] ⊆ ℝ -/
def half_open_interval_left (a b : ℝ) : Set ℝ := {x : ℝ | a < x ∧ x ≤ b}

-- We check that the intersection of (a, b] and [b, c), where a < b < c is {b}
theorem single_point_intersection (a b c : ℝ) (h : a < b ∧ b < c) :
half_open_interval_left a b ∩ half_open_interval_right b c = {b} := by
  rw [half_open_interval_left, half_open_interval_right]
  ext x
  cases' h with hab hbc
  -- Split the ↔ statement
  constructor
  · intro h1
    cases' h1 with hl hr
    apply le_antisymm
    /-
    "le_antisymm" splits the goal of x = b (equivalent to x ∈ {b}) to x ≤ b and x ≥ b
    I learned of this theorem in Section 2.4 of "Mathematics in Lean"
    -/
    · cases' hl with ha1 hb1
      exact hb1
    · cases' hr with hb2 hc2
      exact hb2
  · intro h2
    constructor
    · constructor
      · rw [h2]
        exact hab
      · exact le_of_eq h2
        -- Found by "exact?"
    · constructor
      · exact Eq.ge h2
        -- Found by "exact?"
      · exact lt_of_eq_of_lt h2 hbc
        -- Found by "exact?"

/-
We also show that if x ∈ (a, c), then either x ∈ (a, b] or
x ∈ [b, c) in order to split cases later in our main proof
-/
lemma split_interval {a b c x : ℝ} (h : a < b ∧ b < c) :
(x ∈ open_interval a c) ↔ (x ∈ half_open_interval_left a b ∨ x ∈ half_open_interval_right b c) := by
  rw [open_interval, half_open_interval_left, half_open_interval_right] at *
  constructor
    -- If x ∈ (a, c) then a < x and x < c
  · intro hx
    cases' hx with hax hxc
    -- Split into cases where a < x ≤ b or b < x < c
    by_cases hb : x ≤ b
    · left
      constructor
      exacts [hax, hb] -- or <;> assumption
    · right
      simp only [not_le] at hb
      constructor <;>
      linarith
  · -- this is a really nice example of rcases / rintro:
    rintro (⟨hax, hxb⟩ | ⟨hbx, hxc⟩)
    · exact ⟨hax, by linarith⟩
    · exact ⟨by linarith, hxc⟩

/--
Now, we define what it means for a real function to be uniformly continuous on a subset of ℝ
Recall that a function f : ℝ → ℝ is uniformly continuous
on a set A ⊆ ℝ if for all ε > 0 there exists some δ > 0
such that for all x, y ∈ A, |x - y| < δ implies |f(x) - f(y)| < ε
-/
def uniform_continuous_on (f : ℝ → ℝ) (A : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y, (x ∈ A ∧ y ∈ A) → (|x - y| < δ → |f x - f y| < ε)

/-
As a cursory check, we prove that the identity map on the
set of non-negative numbers is uniformly continuous with
our definition
-/
example : uniform_continuous_on id {x : ℝ | x ≥ 0} := by
  rw [uniform_continuous_on]
  intro ε hε
  -- Since we are working with the identity map, ε also
  -- works as a suitable δ
  use ε
  constructor
  · exact hε
  · intro x y h1 h2
    repeat { rw [id] }
    exact h2

/-- Assume that f
-/
theorem uniform_continuity_interval {a b c : ℝ} {f : ℝ → ℝ} (h : a < b ∧ b < c)
    (hf1 : uniform_continuous_on f (half_open_interval_left a b))
    (hf2 : uniform_continuous_on f (half_open_interval_right b c)) :
    uniform_continuous_on f (open_interval a c) := by
  -- Let ε > 0
  intro ε hε
  have hε2 : ε / 2 > 0 := by linarith
  -- Use the definition of uniform continuity in order to obtain desired δ1
  obtain ⟨δ1, hδ1, h1⟩ := hf1 (ε / 2) hε2
  -- Repeat same logic to obtain δ2
  specialize hf2 (ε / 2) hε2
  cases' hf2 with δ2 htemp2
  cases' htemp2 with hδ2 h2
  -- Proving that δ = min{δ1, δ2} works to show uniform continuity of f on entire interval
  use (min δ1 δ2)
  -- Solving the δ > 0 condition using the fact that δ1, δ2 > 0
  simp only [gt_iff_lt, lt_min hδ1 hδ2, lt_inf_iff, and_imp, true_and]
  -- Introduce arbitrary x, y ∈ (a, c) and corresponding hypotheses
  intro x y hx hy hxyδ1 hxyδ2
  -- rw [split_interval] at hx
  /-
  Using the split_interval lemma did not work here because
  the lemma rewrites hx for an arbitrary number between a and c

  It may be possible to rephrase it in such a way that the
  lemma enables us to choose specific b between a and c

  However, we use the have tactic for now:
  -/
  have haxc : (x ∈ half_open_interval_left a b ∨ x ∈ half_open_interval_right b c) := by
    -- Proof taken from the "→" direction of split_interval proof above
    rw [open_interval, half_open_interval_left, half_open_interval_right] at *
    cases' hx with hax hxc
    -- Split into cases where a < x ≤ b or b < x < c
    by_cases hxb : x ≤ b
    · left
      constructor <;> assumption
    · right
      simp at hxb
      constructor <;>
      linarith
  -- There is probably a much better way to do this, but we repeat the same for y
  have hayc : (y ∈ half_open_interval_left a b ∨ y ∈ half_open_interval_right b c) := by
    rw [open_interval, half_open_interval_left, half_open_interval_right] at *
    cases' hy with hay hyc
    by_cases hyb : y ≤ b
    · left
      constructor
      · exact hay
      · exact hyb
    · right
      simp only [not_le] at hyb
      constructor <;>
      linarith
  -- We show that b belongs to both (a, b] and [b, c) before splitting into cases
  /-
  The symmetry of these arguments implies that there may
  be a more elegant way to do this proof using constructor <:>
  -/
  have hb : b ∈ half_open_interval_left a b ∧ b ∈ half_open_interval_right b c := by
    rw [half_open_interval_left, half_open_interval_right]
    constructor
    · constructor
      · cases' h with hab hbc
        exact hab
      · linarith
    · constructor
      · linarith
      · cases' h with hab hbc
        exact hbc
  -- Splitting into cases depending on which interval (a, b] or [b, c) x and y fall into
  cases haxc with
  | inl haxb =>
    cases hayc with
    | inl hayb =>
      -- Case 1: Both x and y are in (a, b]
      specialize h1 x y
      have haxyb : x ∈ half_open_interval_left a b ∧ y ∈ half_open_interval_left a b :=
        ⟨haxb, hayb⟩
      apply h1 at haxyb
      apply haxyb at hxyδ1
      linarith
    | inr hbyc =>
      -- Case 2: x ∈ (a, b] but y ∈ [b, c)
      specialize h1 x b
      specialize h2 b y
      have hxb : x ∈ half_open_interval_left a b ∧ b ∈ half_open_interval_left a b := by
        constructor
        · exact haxb
        · exact hb.1
      apply h1 at hxb
      have hby : b ∈ half_open_interval_right b c ∧ y ∈ half_open_interval_right b c := by
        simp_all -- this works too
      apply h2 at hby
      -- Proving that x ≤ b ≤ y
      have hxby : x ≤ b ∧ b ≤ y := by
        rw [half_open_interval_left] at haxb
        rw [half_open_interval_right] at hbyc
        -- another way to work with ∧ in a hypothesis is to do .1 or .2 on it
        exact ⟨haxb.2, hbyc.1⟩
      -- Proving that |x - b| ≤ |x - y|
      have hxbxy : |x - b| ≤ |x - y| := by
        cases' hxby with hxleb hbley
        /-
        Invoking "abs_of_nonpos" on |x - b| and |x - y| splits our goal into three parts:
        1) -(x - b) ≤ -(x - y)
        2) x - y ≤ 0
        3) x - b ≤ 0
        -/
        rw [abs_of_nonpos, abs_of_nonpos] <;>
        -- Originally tried to use abs_of_neg, but there could be the case that x = y
        linarith
      -- Proving that |b - y| ≤ |x - y|
      have hbyxy : |b - y| ≤ |x - y| := by
        cases' hxby with hxleb hbley
        rw [abs_of_nonpos, abs_of_nonpos] <;>
        linarith
      have hxbδ1 : |x - b| < δ1 := by
        linarith
      apply hxb at hxbδ1
      have hbyδ2 : |b - y| < δ2 := by
        linarith
      apply hby at hbyδ2
      have hfletemp : |f x - f b + (f b - f y)| ≤ |f x - f b| + |f b - f y| := by
        -- Apply triangle inequality
        exact abs_add (f x - f b) (f b - f y)
      /-
      Establishing this basic equality allows the
      linarith tactic to work in the following have statement
      -/
      have hbasic : |f x - f b + (f b - f y)| = |f x - f y| := by
        norm_num
      -- have hfle : |f x - f y| ≤ |f x - f b| + |f b - f y| := by
      --   linarith
      linarith
  -- We mirror the argument above:
  | inr hbxc =>
    cases hayc with
    | inl hayb =>
      -- Case 3: x ∈ [b, c) but y ∈ (a, b] (similar to Case 2)

      specialize h1 y b
      specialize h2 b x
      have hyb : y ∈ half_open_interval_left a b ∧ b ∈ half_open_interval_left a b := by
        constructor
        · exact hayb
        · cases' hb with hbleft hbright
          exact hbleft
      apply h1 at hyb
      have hbx : b ∈ half_open_interval_right b c ∧ x ∈ half_open_interval_right b c := by
        constructor
        · cases' hb with hbleft hbright
          exact hbright
        · exact hbxc
      apply h2 at hbx
      have hybx : y ≤ b ∧ b ≤ x := by
        rw [half_open_interval_left] at hayb
        rw [half_open_interval_right] at hbxc
        cases' hayb with _ haybright
        cases' hbxc with hbxcleft _
        constructor
        · exact haybright
        · exact hbxcleft
      have hybyx : |y - b| ≤ |y - x| := by
        cases' hybx with hyleb hblex
        rw [abs_of_nonpos, abs_of_nonpos] <;>
        linarith
      have hbxyx : |b - x| ≤ |y - x| := by
        cases' hybx with hyleb hblex
        rw [abs_of_nonpos, abs_of_nonpos] <;>
        linarith
      -- Symmetry of absolute value
      have hsym : |y - x| = |x - y| := by
        exact abs_sub_comm y x
        -- Found by "exact?"
      have hybδ1 : |y - b| < δ1 := by
        linarith
      apply hyb at hybδ1
      have hbxδ2 : |b - x| < δ2 := by
        linarith
      apply hbx at hbxδ2
      have hfletemp : |f x - f b + (f b - f y)| ≤ |f x - f b| + |f b - f y| := by
        exact abs_add (f x - f b) (f b - f y)
      have hbasic : |f x - f b + (f b - f y)| = |f x - f y| := by
        norm_num
      -- have hfle : |f x - f y| ≤ |f x - f b| + |f b - f y| := by
      --   linarith
      -- Symmetry of absolute value
      rw [abs_sub_comm (f y) (f b)] at hybδ1
      rw [abs_sub_comm (f b) (f x)] at hbxδ2
      linarith
    | inr hbyc =>
      -- Case 4: Both x and y are in [b, c)
      specialize h2 x y
      have hbxyc : x ∈ half_open_interval_right b c ∧ y ∈ half_open_interval_right b c := by
        exact ⟨hbxc, hbyc⟩
      apply h2 at hbxyc
      apply hbxyc at hxyδ2
      linarith
