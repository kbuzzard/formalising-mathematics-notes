import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

local notation "ℤ[i]" => GaussianInt

/-
  This file contains a proof of Fermat's theorem on primes which can be written as the sum of two squares.
  We prove this result in four parts, showing that for an odd prime p the following are equivalent:
    (i) p = 1 mod 4 
   (ii) -1 is a QR mod p
  (iii) p is not a prime in ℤ[i]
   (iv) p can be written as a sum of two squares.
  Our strategy is to prove that (i) → (ii), (ii) → (iii), (iii) → (iv), and (iv) → (i). With this, any converse directions can
  be proven just by following around the circle.
-/

/- This first claim is basically just direct from Euler's criterion, which I'm invoking from the library -/
theorem oneimpliestwo (p : ℕ) [Fact (Nat.Prime p)] : (p % 4 = 1) → IsSquare (-1 : ZMod p) := by
  intro hpmod
  have hpform : ∃(k : ℕ), p = 4 * k + 1 := by
    use (p / 4)
    rw [← hpmod]
    exact Eq.symm (Nat.div_add_mod p 4)
  have hpdivtwo : Even (p / 2) := by
    obtain ⟨k, hk⟩ := hpform
    use k
    rw [hk, add_comm, show 4 = 2 * 2 by norm_num, mul_assoc, Nat.add_mul_div_left _ _ Nat.zero_lt_two] -- thanks to yael for reminding me that `show P by`
    ring                                                                                               -- is a thing that i can do.
  have heuler : (-1 : ZMod p) ^ (p / 2) = 1 := Even.neg_one_pow hpdivtwo
  rw [ZMod.euler_criterion _ (by norm_num)]
  exact heuler

/-
  This second one is shows directly that if -1 is a QR, then there is an n such that p | n ^ 2 + 1
  then lifts this divisibility to ℤ[i], where n ^ 2 + 1 factors into n + i and n - i. We can then show that
  p does not divide n + i or n - i, since either would imply p ∣ 1, which is obviously impossible. (i.e. there's a library lemma saying it's imposible)
-/
theorem twoimpliesthree (p : ℕ) [hp : Fact (Nat.Prime p)] : IsSquare (-1 : ZMod p) → ¬Prime (p : ℤ[i]) := by
  intro h
  have hpdivmsqplsone : ∃(n : ℕ), p ∣ (n ^ 2 + 1) := by
    obtain ⟨m, hm⟩ := h
    use (ZMod.val m)
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
    rw [neg_eq_iff_add_eq_zero, ← pow_two, add_comm] at hm
    simp only [Nat.cast_add, Nat.cast_pow, ZMod.natCast_val, ZMod.cast_id', id_eq, Nat.cast_one, hm]
  obtain ⟨n, hn⟩ := hpdivmsqplsone
  have hfactor : (⟨n ^ 2 + 1, 0⟩ : ℤ[i]) = ⟨n, 1⟩ * ⟨n, -1⟩ := by
    simp only [Int.reduceNeg, Zsqrtd.ext_iff, Zsqrtd.mul_re, mul_one, mul_neg, neg_neg,
        add_left_inj, Zsqrtd.mul_im, one_mul, neg_add_cancel, and_true]
    exact pow_two (n : ℤ)
  intro hprime
  obtain ⟨ha, hb, hc⟩ := hprime
  specialize hc ⟨n, 1⟩ ⟨n, -1⟩
  rw [← hfactor] at hc
  have hdivinzi : (⟨p, 0⟩ : ℤ[i]) ∣ ⟨n ^ 2 + 1, 0⟩ := Nat.cast_dvd_cast hn
  apply hc at hdivinzi
  have pdivone : (p : ℤ) ∣ 1 := by -- this is the contradiction we're looking for, and thankfully it doesn't change much with each case.
    cases hdivinzi                 -- Special thanks to Bhavik on suggesting improvements for this section.
    all_goals rename_i hdiv
    all_goals rw [dvd_def] at hdiv ⊢
    all_goals obtain ⟨⟨a,b⟩, hab⟩ := hdiv
    all_goals simp only [Int.reduceNeg, Zsqrtd.ext_iff, Zsqrtd.mul_re, Zsqrtd.natCast_re,
        Zsqrtd.natCast_im, mul_zero, zero_mul, add_zero, Zsqrtd.mul_im] at hab
    · use b
      exact hab.right
    · use -b
      rw [mul_neg, ← neg_eq_iff_eq_neg]
      exact hab.right
  exact Nat.Prime.not_dvd_one hp.out (Int.ofNat_dvd.mp pdivone)

-- Probably a way to avoid this lemma in my proof of threeimpliesfour, but this seemed the simplest way and is a nice thing to have to hand.
lemma int_sum_sq_impl_nat_sum_sq (n : ℕ) : (∃(a b : ℤ), n = a ^ 2 + b ^ 2) -> (∃(u v : ℕ), n = u ^ 2 + v ^ 2) := by
  intro h
  obtain ⟨a, b, hab⟩ := h
  use (Int.natAbs a), (Int.natAbs b)
  rw [← Int.natAbs_cast n]
  simp only [Nat.cast_add, Nat.cast_pow, Int.natCast_natAbs, sq_abs, neg_add_rev, true_or, Int.natAbs_eq_iff, hab]

/-
  This one was the hardest, primarily due to the lemma hanorm. We proceed by showing that if p is not prime in ℤ[i],
  then it isn't irreducible, and in particular there is a nontrivial factorisation p = ax. Taking norms we see that
  p ^ 2 = N(a) N(x). Since a wasn't a unit, N(a) ≠ 1. Since x isn't a unit, N(x) ≠ 1 and so N(a) ≠ p ^ 2. This leaves only
  N(a) = p, and then we can just apply that N(a1 + a2 i) = a1 ^ 2 + a2 ^ 2.
-/
theorem threeimpliesfour (p : ℕ) [hp : Fact (Nat.Prime p)] : ¬Prime (p : ℤ[i]) → ∃(a b : ℕ), p = a ^ 2 + b ^ 2 := by
  intro h
  apply int_sum_sq_impl_nat_sum_sq
  have hnotirred : ¬ Irreducible (⟨p, 0⟩ : ℤ[i]) := by
    contrapose! h
    exact Irreducible.prime h
  rw [irreducible_iff] at hnotirred
  simp only [Int.reduceNeg, not_and, not_forall, Classical.not_imp, not_or] at hnotirred
  have hpnorm : Zsqrtd.norm (⟨p, 0⟩ : ℤ[i]) = p ^2 := by simp only [Zsqrtd.norm, Int.reduceNeg, mul_zero, sub_zero, pow_two]
  have hnotunit : ¬ IsUnit (⟨p, 0⟩ : ℤ[i]) := by
    intro hunit
    rw [← Zsqrtd.norm_eq_one_iff' (by norm_num)] at hunit
    rw [hunit] at hpnorm
    nlinarith [Nat.Prime.one_lt hp.out]
  apply hnotirred at hnotunit
  obtain ⟨⟨a1, a2⟩, ⟨x1, x2⟩, ⟨hax, hanotunit, hxnotunit⟩⟩ := hnotunit
  have hanorm : p = Zsqrtd.norm (⟨a1, a2⟩ : ℤ[i]) := by
    rw [hax, Zsqrtd.norm_mul] at hpnorm
    have hdivpsq : (Zsqrtd.norm (⟨a1, a2⟩ : ℤ[i])) ∣ (p ^ 2) := Dvd.intro (Zsqrtd.norm (⟨x1, x2⟩ : ℤ[i])) hpnorm
    rw [dvd_prime_pow (Nat.prime_iff_prime_int.mp hp.out)] at hdivpsq
    obtain ⟨r, ⟨hr, hrnorm⟩⟩ := hdivpsq
    have hnormnonneg : 0 ≤ Zsqrtd.norm (⟨a1, a2⟩ : ℤ[i]) := GaussianInt.norm_nonneg ⟨a1, a2⟩
    interval_cases r -- since N(a1 + a2 i) ∣ p ^ 2, we know it's of the form ± p ^ r for r ∈ {0, 1, 2}. We split into cases on that.
    all_goals obtain ⟨u, hu⟩ := hrnorm 
    all_goals (fin_cases u) -- for each value of r, split into cases essentially on whether it's p ^ r or -p ^ r.
    all_goals simp only [Int.reduceNeg, Units.val_neg, Units.val_one, mul_neg, mul_one, pow_zero, pow_one] at hu
    repeat on_goal 2 => nlinarith [Nat.Prime.pos hp.out] -- could be done in one line if on_goal supported multiple arguments.
    on_goal 3 => nlinarith [Nat.Prime.pos hp.out]        -- consider PRing batteries to improve the tactic?
    all_goals exfalso                                    -- Still it suffices to close all the "easy" cases.
    · apply hanotunit                                    -- These two remaining cases require a small amount more work.
      rwa [← Zsqrtd.norm_eq_one_iff' (by norm_num)]
    · apply hxnotunit
      rw [← Zsqrtd.norm_eq_one_iff' (by norm_num)]
      have h_psq_ne_zero: (p : ℤ) ^ 2 ≠ (0 : ℤ) := by
        simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero] using NeZero.ne p
      rw [hu] at hpnorm
      exact Int.eq_one_of_mul_eq_self_right (h_psq_ne_zero) hpnorm
  use a1, a2
  simpa only [Zsqrtd.norm, pow_two, Int.reduceNeg, neg_mul, one_mul, sub_neg_eq_add] using hanorm

/-
  This one was easiest, in my opinion. Lean provides very powerful automation with tactics like fin_cases and decide, so
  showing that 3 just isn't a possible value of a ^ 2 + b ^ 2 with a, b : ZMod 4 is very easy. With that in hand, the required contradiction
  is follows quickly. If p is 3 mod 4, then a ^ 2 + b ^ 2 is 3 mod 4, which we just proved can't be done.
-/
theorem fourimpliesone (p : ℕ) (hpodd : Odd p) : (∃(a b : ℕ), p = a ^ 2 + b ^ 2) → (p % 4 = 1) := by 
  intro h
  by_contra hpmod4
  have valsmodfour : ∀(a b : ZMod 4), ¬(a ^ 2 + b ^ 2 = 3) := by decide -- thanks to Niels for telling my about fin_cases.
  have pthreemodfour : p % 4 = 3 := by                                  -- and then Bhavik for suggesting that just decide should work.
    rw [Nat.odd_iff] at hpodd
    cases Nat.odd_mod_four_iff.mp hpodd with
    | inl hone => exfalso; exact hpmod4 hone
    | inr hthree => exact hthree
  obtain ⟨a, b, hab⟩ := h
  rw [hab] at pthreemodfour
  specialize valsmodfour a b
  apply valsmodfour
  rw [pow_two, pow_two, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add, ← ZMod.natCast_zmod_val 3, ZMod.natCast_eq_natCast_iff']
  simpa only [pow_two] using pthreemodfour -- would be nice if simpa could do all this ^ rewriting for me. Sadly i couldn't get it to.

-- Just some examples to demonstrate the results we proved! It's all very neat really.

example : ∃(a b : ℕ), 37 = a ^ 2 + b ^ 2 := by
  have hmod4 : 37 % 4 = 1 := by norm_num
  have hprime : Fact (Nat.Prime 37) := fact_iff.mpr (Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl)
  exact threeimpliesfour 37 (twoimpliesthree 37 (oneimpliestwo 37 hmod4))

example : ¬∃(a b : ℕ), 103 = a ^ 2 + b ^ 2 := by
  have hmod4 : 103 % 4 = 3 := by norm_num
  have hprime : Fact (Nat.Prime 103) := fact_iff.mpr (Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl)
  intro h
  have hothermod4 : 103 % 4 = 1 := fourimpliesone 103 (by decide) h
  rw [hmod4] at hothermod4
  exact Nat.succ_succ_ne_one 1 hothermod4

example : ¬Prime (29 : ℤ[i]) := by
  have h_sum_of_sq : 29 = 2^2 + 5^2 := by norm_num
  have hprime : Fact (Nat.Prime 29) := fact_iff.mpr (Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl)
  have h_mod_4 : 29 % 4 = 1 := fourimpliesone 29 (by decide) (by use 2, 5) -- obviously norm_num can do this, but I'm demonstrating the results.
  have h_neg_one_sq : IsSquare (-1 : ZMod 29) := oneimpliestwo 29 h_mod_4
  exact twoimpliesthree 29 h_neg_one_sq

/- 
  Fermat's two square theorem as it's more commonly stated, which becomes an easy corollary of the previous work.
  Notably, this statement says absolutely nothing about ZMod 4, Zmod p, or ℤ[i]. It's all self-contained in ℕ.
-/
example (p : ℕ) [Fact (Nat.Prime p)] (hodd : Odd p) : (∃(a b : ℕ), p = a ^ 2 + b ^ 2) ↔ p % 4 = 1 := by
  constructor <;> intro h
  · exact fourimpliesone p hodd h -- the easy direction, since we've already proven this.
  · exact threeimpliesfour p (twoimpliesthree p (oneimpliestwo p h)) -- following the circle around to get the result. Proofs as functions is very convenient.
