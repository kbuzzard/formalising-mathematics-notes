import Mathlib

/-- In this project, I will prove Squeeze Theorem for sequences:
'Let (aₙ), (bₙ), (cₙ) be sequences of real numbers.
Suppose that there exists an integer N such that bₙ ≤ aₙ ≤ cₙ for all n > N.
If both (aₙ) and (cₙ) converge to the same real number L,
then (bₙ) also converges to L.'
Also, example is given to show how to use the theorem. --/

-- # Proof of squeeze theorem

-- Define the limit of a sequence (from Section2sheet3)
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

-- For any ε > 0, there is an N such that for all n ≥ N, |a n - t| < ε
lemma abs_diff_small_of_tendsTo {a : ℕ → ℝ} {t : ℝ}
    (h : TendsTo a t) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε := by
  apply h
  exact hε

-- If |x| < ε then -ε < x < ε
lemma abs_lt_implies_bounds {x ε : ℝ} (h : |x| < ε) : -ε < x ∧ x < ε := by
  constructor
  -- Prove -ε < x
  · apply neg_lt_of_abs_lt
    exact h
  -- Prove x < ε
  · apply lt_of_abs_lt
    exact h

-- If -ε < x < ε then |x| < ε
lemma bounds_implies_abs_lt {x ε : ℝ} (h : -ε < x ∧ x < ε) : |x| < ε := by
  cases' h with h1 h2
  exact abs_lt.mpr ⟨h1, h2⟩

-- Transitivity of sequence bounds
lemma seq_bounds {a b c : ℕ → ℝ} (h : ∀ n : ℕ, a n ≤ b n ∧ b n ≤ c n) :
    ∀ n : ℕ, a n ≤ c n := by
  intro n
  #check (h n)
  exact le_trans (h n).1 (h n).2

-- If a ≤ b ≤ c and -ε < a - L and c - L < ε then |b - L| < ε
lemma squeeze_bounds {a b c L ε : ℝ}
    (h1 : a ≤ b) (h2 : b ≤ c) (h3 : -ε < a - L) (h4 : c - L < ε) :
    |b - L| < ε := by
  apply bounds_implies_abs_lt
  constructor
  -- Prove -ε < b - L
  · calc
      -ε < a - L := h3
      _ ≤ b - L := sub_le_sub_right h1 L
  -- Prove b - L < ε
  · calc
      b - L ≤ c - L := sub_le_sub_right h2 L
      _ < ε := h4

-- Squeeze Theorem
theorem squeeze_theorem {a b c : ℕ → ℝ} {L : ℝ}
    (h_bounds : ∃ N₀ : ℕ, ∀ n ≥ N₀, a n ≤ b n ∧ b n ≤ c n)
    (h_lim_a : TendsTo a L)
    (h_lim_c : TendsTo c L) :
    TendsTo b L := by
  rw [TendsTo]
  intro ε hε
  -- Get N0 from bounds condition
  cases' h_bounds with N0 hN0
  -- Get N1 from limit of a
  rw [TendsTo] at h_lim_a
  have h_a := h_lim_a ε hε
  cases' h_a with N1 hN1
  -- Get N2 from limit of c
  rw [TendsTo] at h_lim_c
  have h_c := h_lim_c ε hε
  cases' h_c with N2 hN2
  -- Take maximum of all bounds
  let N := max N0 (max N1 N2)
  use N
  intro n hn
  -- Break down inequality chain for bounds
  have hN0_left : N0 ≤ N := by
    exact le_max_left N0 (max N1 N2)
  have hN0_trans : N0 ≤ n := by
    exact le_trans hN0_left hn
  -- Get bounds for this n
  have h_bounds_n : a n ≤ b n ∧ b n ≤ c n := by
    exact hN0 n hN0_trans
  -- Similar breakdown for a_n bounds
  have hN1_right : N1 ≤ max N1 N2 := by
    exact le_max_left N1 N2
  have hN1_trans : N1 ≤ N := by
    exact le_trans hN1_right (le_max_right N0 (max N1 N2))
  have hN1_final : N1 ≤ n := by
    exact le_trans hN1_trans hn
  -- Get bounds for a_n
  have h_a_n := hN1 n hN1_final
  have ⟨h_a_lower, h_a_upper⟩ := abs_lt_implies_bounds h_a_n
  -- Similar breakdown for c_n bounds
  have hN2_right : N2 ≤ max N1 N2 := by
    exact le_max_right N1 N2
  have hN2_trans : N2 ≤ N := by
    exact le_trans hN2_right (le_max_right N0 (max N1 N2))
  have hN2_final : N2 ≤ n := by
    exact le_trans hN2_trans hn
  -- Get bounds for c_n
  have h_c_n := hN2 n hN2_final
  have ⟨h_c_lower, h_c_upper⟩ := abs_lt_implies_bounds h_c_n
  -- Apply squeeze
  exact squeeze_bounds h_bounds_n.1 h_bounds_n.2 h_a_lower h_c_upper

-- # Example using squeeze theorem

-- Prove that 2 / (n + 1) → 0
theorem conv_two_over_n : TendsTo (fun n => 2 / (n + 1 : ℝ)) 0 := by
  -- Squeeze 2 / (n + 1) between 0 and 3 / n
  apply squeeze_theorem
  case a => exact fun n ↦ 0 -- by Kevin
  case c => exact fun n => 3 / n
  -- Show bounds 0 ≤ 2 / (n + 1) ≤ 3 / n for n ≥ 2
  · use 2
    intro n hn
    constructor
    -- Show 0 ≤ 2 / (n + 1)
    · apply div_nonneg
      · norm_num
      · #check (Nat.cast_add_one_pos n).le
        exact (Nat.cast_add_one_pos n).le
    -- Show 2 / (n + 1) ≤ 3 / n
    · have h1 : (n : ℝ) ≥ 2 := by exact_mod_cast hn
      have h2 : (n : ℝ) > 0 := by
        apply lt_of_lt_of_le
        · show (0 : ℝ) < 2
          norm_num
        · exact h1
      have h3 : 2 * n ≤ 3 * (n + 1) := by
        calc 2 * n ≤ 2 * n + 2 := by simp
             _ ≤ 3 * n + 3 := by linarith
             _ = 3 * (n + 1) := by ring
      apply div_le_div₀
      · norm_num
      · norm_num
      · exact h2
      · norm_num
  -- Show lower sequence (constant 0) converges to 0
  · intro ε hε
    exists 0
    intro n _
    simp
    exact hε
  -- Show upper sequence (3 / n) converges to 0
  · intro ε hε
    exists (Nat.ceil (3 / ε) + 1) -- + 1 to avoid (3 / ε) = Nat.ceil (3 / ε) = n
    intro n hn
    simp
    -- Show that 3 / ε < n
    have h1 : 3 / ε ≤ ⌈3 / ε⌉₊ := Nat.le_ceil (3 / ε)
    have h2 : 3 / ε + 1 ≤ ⌈3 / ε⌉₊ + 1 := add_le_add_right h1 1
    have h3 : (3 / ε + 1 : ℝ) ≤ n := by
      apply le_trans _ (Nat.cast_le.mpr hn)
      simp
      exact h1
    have h4 : 3 / ε < ↑n := by
      exact lt_of_lt_of_le (lt_add_one (3 / ε)) h3
    -- show that n > 0
    have hn_pos : (n : ℝ) > 0 := by
      apply lt_trans _ h4
      apply div_pos
      · norm_num
      · exact hε
    -- Remove absolute value: |3 / n| = 3 / n since it's positive
    rw [abs_of_pos (div_pos (by norm_num) hn_pos)]
    -- Transform 3 / ε < ↑n to 3 / ↑n < ε

    -- Failed attempt
    -- rw [div_lt_comm] at h4
    -- exact h4

    have hε_ne_zero : ε ≠ 0 := ne_of_gt hε
    -- Multiply both sides by ε > 0
    rw [← mul_lt_mul_right hε] at h4
    -- Now h4 is: (3 / ε * ε < n * ε)
    -- Simplify left side using division and multiplication
    have h5 : ε * (3 / ε) = 3 := by
      rw [mul_comm (3 / ε) ε] at h4
      exact mul_div_cancel₀ 3 hε_ne_zero
    -- Transfrom h4 to 3 < n * ε
    rw [mul_comm (3 / ε) ε] at h4
    rw [h5] at h4
    -- Divide both sides by n > 0
    have h6 : 3 / n < ε := by
      apply (div_lt_iff₀ hn_pos).mpr
      rw [mul_comm] at h4
      exact h4
    exact h6
