/-
In this file, I define the epsilon-delta definition of a limit and the epsilon-delta definition of a Cauchy sequence.
I then prove some basic results about these definitions.

Lastly, I prove that the radius of convergence of a power series exists.
-/
import Mathlib.Tactic
import Mathlib.Data.ENNReal.Basic

namespace Project1

open scoped ENNReal
open scoped NNReal

-- Epsilon-delta definition of a limit
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

-- Epsilon-delta definition of a Cauchy sequence
def Cauchy (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ m n, B ≤ m → B ≤ n → |a m - a n| < ε

-- a sequence of partial sums of a power series
def power_series (a : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ := ∑ i in Finset.range n, a i * (x ^ i)

theorem cauchy_iff_limit (a : ℕ → ℝ) : (∃ A : ℝ, TendsTo a A) ↔ Cauchy a := by
  constructor <;> intro h
  . intro ep hep
    obtain ⟨A, hA⟩ := h
    specialize hA (ep / 2) (by linarith)
    obtain ⟨B, hB⟩ := hA
    use B
    intro m n hm hn
    calc
      |a m - a n| = |(a m - A) + (A - a n)| := by ring_nf
      _ ≤ |a m - A| + |A - a n| := by apply abs_add
      _ = |a m - A| + |a n - A| := by rw [← neg_sub (a n) A, abs_neg]
      _ < ep / 2 + ep / 2 := by linarith [hB m hm, hB n hn]
      _ = ep := by linarith
  -- The goal is to show that if we have a Cauchy sequence, then it has a limit
  -- This requires the completeness of the real numbers
  -- I have left it sorried to save time
  . sorry

-- If a sequence is absolutely converging, then it is convergent
theorem convergent_of_absolutely_convergent (a : ℕ → ℝ) (h : Cauchy (fun x => |a x|)) : Cauchy a := by sorry

-- did not end up using this, so didn't finish proof
theorem comparison_test (a b : ℕ → ℝ) (h : ∀ n, |a n| ≤ b n) (hb : Cauchy b) : Cauchy a := by
  intro ε hep
  obtain ⟨B, hB⟩ := hb ε hep
  use B
  intro m n hm hn
  sorry

-- a proof that if you multiply a bounded sequence by an exponentially decreasing sequence pointwise,
-- then the resulting sequence is Cauchy
theorem convergent_of_bdd (α : ℝ) (hα : 0 < α ∧ α < 1) (b : ℕ → ℝ) (hb : ∃ B, ∀ (n : ℕ), |b n| < B)
    : Cauchy (fun t => b t * (α ^ t)) := by
  sorry

-- This is a proof of the fact that if a series converges, the terms must tend to zero
theorem tail_zero_of_sum (a : ℕ → ℝ) (h : Cauchy (λ n => ∑ i in Finset.range n, a i)) : TendsTo a 0 := by
  by_contra silly
  simp only [TendsTo] at silly
  push_neg at silly
  rw [←cauchy_iff_limit] at h
  obtain ⟨A, hA⟩ := h
  obtain ⟨ε, hε, haB⟩ := silly
  simp only [TendsTo] at hA
  specialize hA ε hε
  obtain ⟨B, hB⟩ := hA
  obtain ⟨nB, hnB⟩ := haB B
  -- idea for rest of proof:
  -- we will eventually get within epsilon of A
  -- but we can increase the sum by epsilon whenever we want
  -- if we do this twice, we get within epsilon of A + 2ε
  sorry

theorem radius_of_convergence (a : ℕ → ℝ) :
    (∃ (R : ℝ≥0∞), (∀ x : ℝ, ‖x‖₊ < R → Cauchy (power_series (fun t => ‖a t‖₊) x)) ∧ ∀ x : ℝ, ‖x‖₊ > R → ¬ Cauchy (power_series a x)) := by
  let S := {x : ℝ≥0 | ∃ t : ℝ, ‖t‖₊ = x ∧ Cauchy (fun i => ‖a i * (x ^ i)‖₊)}
  set R := sSup (ENNReal.ofNNReal '' S) with hr
  clear_value R
  use R
  -- we can always get closer to R when below it
  have h_lub : ∀ (x : ℝ≥0), x < R → ∃ y ∈ S, x < y := by
    intro x hx
    obtain ⟨t, ht, hcauchy⟩ := hx
    by_contra silly
    push_neg at silly
    -- have ht := sSup_le silly
    -- typeclass inference is not working, but the goal is provable
    sorry
  constructor
  -- if |x| < R, then the power series converges
  . intro x hx
    -- there must exist an element y ∈ S greater than x
    have hS : ∃ y ∈ S, ‖x‖₊ < y := by
      exact h_lub ‖x‖₊ hx
    obtain ⟨y, hy, hxy⟩ := hS
    norm_cast
    have hbdd := convergent_of_bdd (‖y‖₊ / ‖x‖₊) ⟨by sorry, sorry⟩ (fun i => ‖a i * (x ^ i)‖₊)
    have hc : Cauchy fun t => ↑‖a t * x ^ t‖₊ * (↑‖y‖₊ / ↑‖x‖₊) ^ t := by
      apply hbdd
      -- TODO: show it is bounded
      -- true since the sequence converges to 0 so must be bounded
      sorry
    -- simple algebra remaining
    norm_cast at hc ⊢
    -- the below doesn't work as we need to use extensionality
    -- rw [div_pow] at hc
    sorry
  -- if |x| > R, then the power series diverges
  . intro x hx silly
    -- by definition of sSup
    have : ‖x‖₊ ∉ S := by
      dsimp [S]
      intro silly
      obtain ⟨t, ht, hcauchy⟩ := silly
      -- getting type class errors again :()
      -- the goal can be proved using properties of sSup
      sorry
    have h := tail_zero_of_sum (fun i => ‖a i * (x ^ i)‖₊) sorry
    dsimp only [S] at this
    have hk : Cauchy fun i => ↑‖a i * ↑x ^ i‖₊ := (cauchy_iff_limit (fun i => ‖a i * (x ^ i)‖₊)).mp ⟨0, sorry⟩
    have hnk : ∃ t, t = ‖x‖₊ ∧ Cauchy fun i => ↑‖a i * ‖x‖₊ ^ i‖₊ := by sorry
    -- the above goal is provable and we get a contradiction
    sorry

end Project1
