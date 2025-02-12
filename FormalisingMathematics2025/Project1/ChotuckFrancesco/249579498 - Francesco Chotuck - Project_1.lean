import Mathlib.Tactic -- Import all the tactics from Mathlib

/-!
This file provides formal definitions and theorems for
continuity of real-valued functions on the real numbers.
It includes:

1. The definition of a `limit` of a function at a point.
2. Definitions for different types of `continuity`:
   - Continuity at a point.
   - `Left-continuity` and `right-continuity.`
   - Continuity on various intervals: `open`, `closed`, `half-open intervals`.
3. Proving the continuity of a constant function.
4. A theorem proving the equivalence between continuity at a point and the combination of
   left-continuity and right-continuity.
-/

/--
# The definition of a limit
We say that `f` has a limit `L` as `x` approaches `c` if for every `ε > 0`,
there exists a `δ > 0` such that for all `x` satisfying `0 < |x - c| < δ`,
we have `|f(x) - L| < ε`.
-/

def limit (f : ℝ → ℝ) (L c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - c| ∧ |x - c| < δ → |f x - L| < ε

/--
# The definition of a left limit
We say that `f` has a left limit `L` as `x` approaches `c` from the left
if for every `ε > 0`, there exists a `δ > 0` such that for all `x` satisfying
`c - δ < x < c`, we have `|f(x) - L| < ε`.
-/
def left_limit (f : ℝ → ℝ) (L c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, c - δ < x ∧ x < c → |f x - L| < ε

/--
# The definition of a right limit
We say that `f` has a right limit `L` as `x` approaches `c` from the right
if for every `ε > 0`, there exists a `δ > 0` such that for all `x` satisfying
`c < x < c + δ`, we have `|f(x) - L| < ε`.
-/
def right_limit (f : ℝ → ℝ) (L c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, c < x ∧ x < c + δ → |f x - L| < ε

/--
# The definitions of the types of continutity
A function `f` is continuous at a point `c` if the limit of `f` at `c` equals `f(c)`.
This definition relies on the `limit` predicate.
-/
def continuous_at (f : ℝ → ℝ) (c : ℝ) : Prop :=
  limit f (f c) c

/--
A function `f` is left-continuous at a point `c`
if the limit of `f(x)` as `x` approaches `c` from the left equals `f(c)`.
-/
def left_continuous_at (f : ℝ → ℝ) (c : ℝ) : Prop :=
  left_limit f (f c) c

/--
A function `f` is right-continuous at a point `c`
if the limit of `f(x)` as `x` approaches `c` from the right equals `f(c)`.
-/
def right_continuous_at (f : ℝ → ℝ) (c : ℝ) : Prop :=
  right_limit f (f c) c

/--
A function `f` is continuous on an open interval `(a, b)`
if it is continuous at every point `c` in `(a, b)`.
-/
def continuous_on_open_interval (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ c : ℝ, a < c ∧ c < b → continuous_at f c

/--
A function `f` is continuous on a closed interval `[a, b]`
if it is continuous at every point `c` in `(a, b)`,
right-continuous at `a`, and left-continuous at `b`.
-/
def continuous_on_closed_interval (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  continuous_on_open_interval f a b ∧
  right_continuous_at f a ∧ left_continuous_at f b

/--
A function `f` is continuous on a half-open interval `(a, b]`
if it is continuous at every point `c` in `(a, b)`,
and left-continuous at `b`.
-/
def continuous_on_right_half_open_interval (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  continuous_on_open_interval f a b ∧ left_continuous_at f b

/--
A function `f` is continuous on a half-open interval `[a, b)`
if it is continuous at every point `c` in `(a, b)`,
and right-continuous at `a`.
-/
def continuous_on_left_half_open_interval (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  continuous_on_open_interval f a b ∧ right_continuous_at f a

/--
A function `f` is continuous on the entire real line if it is continuous at every point `c` in ℝ.
-/
def continuous (f : ℝ → ℝ) : Prop :=
  ∀ c : ℝ, continuous_at f c

/--
# A basic result on continuity
An example property: If `f` is a constant function, then it is continuous.
-/

theorem continuous_of_constant (k : ℝ) : continuous (fun x => k) := by
  -- Introduce the point `c` and the ε > 0 condition for continuity.
  intro c ε hε
  -- Choose δ = 1 as the value to satisfy the continuity condition.
  use 1
  -- Show that δ > 0 (required by the ε-δ definition).
  constructor
  · linarith -- Automatically proves δ > 0 since δ = 1 is positive.
  -- Prove the second part of the ε-δ definition.
  · intro y hy -- Assume a point `y` satisfies |y - c| < δ.
    simp -- Simplify the goal, as the function is constant (|k - k| = 0).
    exact hε -- Since ε > 0 was given, the condition is trivially satisfied.

/--
# Helper lemma 1
This lemma states that if a function `f`
is both left-continuous and right-continuous at a point `c`,
then `f` is continuous at `c`.
-/

lemma continuous_at_of_left_and_right_continuous {f : ℝ → ℝ} {c : ℝ} :
  left_continuous_at f c ∧ right_continuous_at f c → continuous_at f c := by
  intro h
  -- Split the conjunction into left- and right-continuity assumptions
  cases' h with h_left h_right
  -- Rewrite the definition of `continuous_at` and `limit`
  rw [continuous_at, limit]
  intro ε hε
  -- From left-continuity, obtain δ₁ > 0
  obtain ⟨δ₁, hδ₁, h_left_cond⟩ := h_left ε hε
  -- From right-continuity, obtain δ₂ > 0
  obtain ⟨δ₂, hδ₂, h_right_cond⟩ := h_right ε hε
  -- Define δ as the minimum of δ₁ and δ₂
  let δ := min δ₁ δ₂
  have hδ : δ > 0 := lt_min hδ₁ hδ₂
  -- Use δ to prove continuity
  use δ
  constructor
  · exact hδ -- Prove δ > 0
  · -- Prove the continuity condition
    intros x hx
    rw [abs_lt] at hx
    cases' hx with h_left_bound h_right_bound
    by_cases h_case : x < c
    · -- Case: x < c, use left-continuity
      apply h_left_cond
      constructor
      · have : δ ≤ δ₁ := min_le_left δ₁ δ₂
        linarith -- Prove c - δ < x
      · exact h_case -- Prove x < c
    · -- Case: x ≥ c, use right-continuity
      apply h_right_cond
      constructor
      · -- Prove c < x
        have h_geq : c ≤ x := not_lt.mp h_case
        have h_neq : c ≠ x := by
          aesop
        have h_gt : c < x := lt_of_le_of_ne h_geq h_neq
        exact h_gt
      · -- Prove x < c + δ
        have : δ ≤ δ₂ := min_le_right δ₁ δ₂
        linarith

/--
# Helper lemma 2
This lemma states that if a function `f` is continuous at a point `c`,
then it is both left-continuous and right-continuous at `c`.
-/

lemma continuous_at_implies_left_and_right_continuous (f : ℝ → ℝ) (c : ℝ) :
  continuous_at f c → left_continuous_at f c ∧ right_continuous_at f c := by
  -- Assume `f` is continuous at `c`
  intro h_cont
  -- Split the goal into proving left- and right-continuity
  constructor
  · -- Prove left-continuity at `c`
    intro ε hε -- Assume ε > 0
    -- Since `f` is continuous at `c`, obtain δ > 0 such that the global continuity condition holds
    obtain ⟨δ, hδ, h⟩ := h_cont ε hε
    -- Use the same δ for left-continuity
    use δ
    constructor
    · -- Prove δ > 0
      exact hδ
    · -- Prove the left-continuity condition
      intro x hx -- Assume `x` is in the left-neighborhood of `c`, i.e., `c - δ < x < c`
      -- Apply the global continuity condition
      apply h
      constructor
      · -- Prove `0 < |x - c|`
        rw [abs_pos]
        linarith
      · -- Prove `|x - c| < δ`
        rw [abs_lt]
        constructor
        · linarith -- Prove `x - c > -δ`
        · linarith -- Prove `x - c < δ`
  · -- Prove right-continuity at `c`
    intro ε hε -- Assume ε > 0
    -- Since `f` is continuous at `c`, obtain δ > 0 such that the global continuity condition holds
    obtain ⟨δ, hδ, h⟩ := h_cont ε hε
    -- Use the same δ for right-continuity
    use δ
    constructor
    · -- Prove δ > 0
      exact hδ
    · -- Prove the right-continuity condition
      intro x hx -- Assume `x` is in the right-neighborhood of `c`, i.e., `c < x < c + δ`
      -- Apply the global continuity condition
      apply h
      constructor
      · -- Prove `0 < |x - c|`
        rw [abs_pos]
        linarith
      · -- Prove `|x - c| < δ`
        rw [abs_lt]
        constructor
        · linarith -- Prove `x - c > -δ`
        · linarith -- Prove `x - c < δ`

/--
# The main theorem
A function `f` is continuous at a point `c` if and only if
it is both left-continuous and right-continuous at `c`.
-/

theorem continuous_at_iff_left_and_right_continuous (f : ℝ → ℝ) (c : ℝ) :
  continuous_at f c ↔ left_continuous_at f c ∧ right_continuous_at f c := by
  constructor
  · -- (⇒) If `f` is continuous at `c`, then it is left- and right-continuous
    apply continuous_at_implies_left_and_right_continuous
  · -- (⇐) If `f` is left- and right-continuous at `c`, then it is continuous at `c`
    intro h
    exact continuous_at_of_left_and_right_continuous h

#lint
