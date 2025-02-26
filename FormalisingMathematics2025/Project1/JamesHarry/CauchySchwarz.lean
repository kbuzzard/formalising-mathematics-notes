import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic

/- Creates variable F of type Type*.
Type*, shorthand for Type u, means Lean will try and infer the universe level. -/
variable {n : ℕ}
variable {F : Type*}

/- F is a real vector space with an inner product on it. -/
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

-- local notation "⟪" x ", " y "⟫" => @inner ℝ F _ x y
open scoped RealInnerProductSpace
-- BM: I'm guessing you figured out the notation from the file defining InnerProductSpace, but that
-- line also tells you how to turn it on!

/- The inner product of any vectors x, y in F with ‖x‖ = ‖y‖ = 1 is
less than or equal to the product of their norms. -/
lemma cauchy_schwarz_norm_one (x y : F) (h1 : ‖x‖ = 1) (h2 : ‖y‖ = 1) : ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := by
  have h3 : 0 ≤ 2 - 2 * ⟪x, y⟫ := by
    calc
      0 ≤ ‖x - y‖^2 := sq_nonneg ‖x - y‖
      _ = ⟪x - y, x - y⟫ := by rw [← real_inner_self_eq_norm_sq]
      _ = ⟪x, x⟫ + ⟪y, y⟫ - 2 * ⟪x, y⟫ := by rw [real_inner_sub_sub_self]; ring
      _ = 2 - 2 * ⟪x, y⟫ := by
        rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, h1, h2]; ring;
  replace h3 : ⟪x, y⟫ ≤ (1 : ℝ) := by simpa using h3
  simp [h1, h2, h3]

-- Any vector x≠0 can be rewritten as a product of a non negative real and a vector with norm 1
lemma rewrite_norm_one (x : F) (hx : x ≠ 0) :
    ∃ (a : ℝ), ∃ (x' : F), x = a • x' ∧ ‖x'‖ = 1 ∧ 0 ≤ a := by
  use ‖x‖, ‖x‖⁻¹ • x
  simp [smul_inv_smul₀, norm_smul, hx]

/- The inner product of any vectors x, y in F is less than or equal to the product of their
norms. -/
theorem cauchy_schwarz (x y : F) : ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := by
  by_cases hx : x = 0
  · simp [hx]
  /- BM: while usual style is to have

  cases ...
  · sorry
  · sorry

  it's also okay to have

  cases ...
  · sorry
  sorry

  especially if the second case is much longer than the first. This doesn't break the rules, since
  at no point do you have two active goals
  -/

  rcases eq_or_ne y 0 with rfl | hy
  -- BM: the rcases/rfl trick is a nice one to know
  -- `rfl` is hardcoded into rcases/rintro/obtain to introduce the equality, and then substitute
  -- everywhere with it
  · simp
  obtain ⟨a, x', rfl, h1, h2⟩ := rewrite_norm_one x hx
  obtain ⟨b, y', rfl, h3, h4⟩ := rewrite_norm_one y hy

  calc
    inner (a • x') (b • y') ≤ a * (b * inner x' y') := by
      rw [real_inner_smul_left, real_inner_smul_right]
    _ = (a * b) * inner x' y' := by ring
    _ ≤ a * b * (‖x'‖ * ‖y'‖) := by gcongr; exact cauchy_schwarz_norm_one x' y' h1 h3
    _ = a * ‖x'‖ * (b * ‖y'‖) := by ring
    _ ≤ ‖a • x'‖ * ‖b • y'‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg h2, Real.norm_of_nonneg h4]

/- The absolute value of the inner product of any vectors x, y in F is less than or equal to
the product of their norms. -/
theorem abs_cauchy_schwarz (x y : F) : |⟪x, y⟫| ≤ ‖x‖ * ‖y‖ := by
  have h1 : ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := cauchy_schwarz x y

  have h2 : -⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := by
    have h3 := cauchy_schwarz (-x) y
    rwa [norm_neg, inner_neg_left x y] at h3

  simp [abs_le', *]
