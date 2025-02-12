import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic

/- Creates variable F of type Type*.
Type*, shorthand for Type u, means Lean will try and infer the universe level. -/
variable {n : ℕ}
variable {F : Type*}

/- F is a real vector space with an inner product on it. -/
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => @inner ℝ F _ x y

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
lemma rewrite_norm_one (x : F) (hx : ¬x = 0) :
  ∃ (a : ℝ), ∃ (x' : F), x = a • x' ∧ ‖x'‖ = 1 ∧ 0 ≤ a := by
  use ‖x‖
  use ‖x‖⁻¹ • x
  constructor
  · rw [smul_inv_smul₀]
    -- mpr is modus ponens reversed, If a ↔ b and b, then a
    exact norm_ne_zero_iff.mpr hx
  · constructor
    -- rewrite ‖‖x‖⁻¹ • x‖ = 1 as ‖x‖⁻¹ • ‖x‖ = 1 and use x ≠ 0 to prove
    · simp [norm_smul, hx]
    · exact norm_nonneg x

/- The inner product of any vectors x, y in F is less than or equal to the product of their
norms. -/
theorem cauchy_schwarz (x y : F) : ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · obtain ⟨a, x', rfl, h1, h2⟩ := rewrite_norm_one x hx
      obtain ⟨b, y', rfl, h3, h4⟩ := rewrite_norm_one y hy

      simp only [real_inner_smul_left, real_inner_smul_right, norm_smul]
      simp only [Real.norm_of_nonneg h2, Real.norm_of_nonneg h4]

      ring_nf
      nth_rewrite 2 [mul_assoc]

      -- both sides of the inequality scale by a factor of λμ
      apply mul_le_mul_of_nonneg_left
      · exact cauchy_schwarz_norm_one x' y' h1 h3
      · exact mul_nonneg h4 h2

/- The absolute value of the inner product of any vectors x, y in F is less than or equal to
the product of their norms. -/
theorem abs_cauchy_schwarz (x y : F) : |⟪x, y⟫| ≤ ‖x‖ * ‖y‖ := by
  have h1 : ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := by
    exact cauchy_schwarz x y

  have h2 : -⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := by
    have h3 := cauchy_schwarz (-x) y
    rw [norm_neg, inner_neg_left x y] at h3
    exact h3

  rw [abs]
  exact sup_le h1 h2
