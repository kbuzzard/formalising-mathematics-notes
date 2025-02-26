/-
Copyright (c) 2025 Steven Herbert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Herbert
-/

import Mathlib

/-!
This file formalises some elementary results in number theory leading to a special case of the
fundamental theorem of arithmetic: that semiprimes have a unique factorisation

## Main results

- `Euclids_lemma` and `Euclids_lemma_alternative` : two formats of Euclid's lemma
- `Semi_Primes_Unique_Factorisation`          : semiprimes have a unique factorisation

## Organisation

The file is organised in three sections: (I), some simple facts about what it means to be a prime, a
divisor, a greatest common divisor etc; (II), we give some non-trivial lemmas that at then used in
the final part; (III) the main result.
-/

-- # Section I: Simple preliminary facts

/- First we check a couple of things that we use heavily, namely that `gcd` and `∣` treat `0`
in a standard way (here the value `5` has been chosen arbitrarily) -/
#eval gcd 5 0 -- which is `5` as expected
#eval 5 ∣ 0 -- to confirm it is `true` that integers divide `0`

-- Lemma : if `a` divides prime `p` it is either `1` or `p`
lemma Prime_Factors (a p : ℤ) (hp : 0 < p) (ha : 0 < a) (h1 : Prime p) (h2 : a ∣ p) :
    a = 1 ∨ a = p := by
  lift a to ℕ using ha.le
  lift p to ℕ using hp.le
  simp only [Nat.cast_pos, Nat.cast_eq_one, Nat.cast_inj] at *
  rw [Int.natCast_dvd_natCast] at h2
  rw [Int.prime_iff_natAbs_prime, Int.natAbs_ofNat, Nat.prime_def] at h1
  exact h1.2 a h2
  done

-- this one was false!!
example : ∃ a p : ℤ, Prime p ∧ a ∣ p ∧ ¬ (a = 1 ∨ a = p) := by
  use (-5), 5, by norm_num, by norm_num, by norm_num

lemma gcd_pos {a b : ℤ} (ha : 0 < a) : 0 < gcd a b := by
  rw [← Int.coe_gcd, Nat.cast_pos, Int.gcd_pos_iff]
  exact Or.inl ha.ne'

/- Lemma : if `p` is prime, and an integer `a` is such that `p ∣ a` then the greatest common divisor
of `p` and `a` is `p` -/
lemma Simple_GCD_lemma_1 {p a : ℤ} (hp : 0 < p) (h1 : p ∣ a) : -- h2 wasn't needed!
    gcd p a = p := by
  -- As `p` is a prime (from `h2`) it is positive
  -- BM: ^ this might be where you went wrong: an integer being prime in Lean doesn't mean it's
  -- positive
  -- If a positive number, `p`, divides `q`, then `GCD(p,q)` is certainly `p`
  -- Theorem `GCDNat.gcd_eq_left` is close to what we need, but for naturals not all integers
  rwa [gcd_eq_left_iff]
  rw [Int.normalize_of_nonneg hp.le]
  done

/- Lemma : if `p` is prime, and an integer `a` is such that `¬ (p ∣ a)` then the greatest common
divisor of `p` and `a` is `1` -/
lemma Simple_GCD_lemma_2 {p a : ℤ} (hp : 0 < p) (h1 : ¬ p ∣ a) (h2 : Prime p) :
    gcd p a = 1 := by
  have h3 : gcd p a ∣ p := gcd_dvd_left p a
  have h4 : gcd p a ∣ a := gcd_dvd_right p a
  -- `gcd p a` certainly divides each of `p` and `a` (`h3` and `h4` respectively)
  have h5 : gcd p a = 1 ∨ gcd p a = p := Prime_Factors (gcd p a) p hp (gcd_pos hp) h2 h3
  -- as `p` is prime, `gcd p a` is either `1` or `p`
  aesop
  -- together `h3`, `h4` and `h5` leave `gcd p q = 1` as the only possibility
  done

-- Lemma : if `p1` and `p2` are distinct primes, then they are co-prime
lemma Primes_are_Coprime {p1 p2 : ℤ} (hp1 : 0 < p1) (hp2 : 0 < p2) (h1 : Prime p1)
    (h2 : Prime p2) (h3 : p1 ≠ p2) : gcd p1 p2 = 1 := by
  have h4 : gcd p1 p2 ∣ p1 := gcd_dvd_left p1 p2
  have h5 : gcd p1 p2 ∣ p2 := gcd_dvd_right p1 p2
  -- First we establish that `gcd p1, p2` divides each of `p1` and `p2` (`h4` and `h5` respectively)
  have h6 : gcd p1 p2 = 1 ∨ gcd p1 p2 = p1 :=
    Prime_Factors (gcd p1 p2) p1 hp1 (gcd_pos hp1) h1 h4
  have h7 : gcd p1 p2 = 1 ∨ gcd p1 p2 = p2 :=
    Prime_Factors (gcd p1 p2) p2 hp2 (gcd_pos hp1) h2 h5
  /- Second we use the fact that each of `p1` and `p2` are prime to come up with
  possible values of `gcd p1 p2` using h4 and h5 -/
  aesop
   -- Finally, from the fact that `h3`, `h6` and `h7` all hold, we deduce `gcd p1 p2 = 1`
  done

-- Lemma : if an integer divides each of two integers, it divides their sum
lemma Divide_Sum_Lemma {w x y z : ℤ} (h1 : x + y = z) (h2 : w ∣ x) (h3 : w ∣ y) : w ∣ z := by
  have h4 : ∃ a : ℤ , x = w * a := by trivial
  -- `w` divides `x`, so `x` can be written `w * a`
  cases' h4 with a h4
  -- make the `a` in `h4` a variable
  have h5 : ∃ b : ℤ , y = w * b := by trivial
  -- `w` divides `y`, so `y` can be written `w * b`
  cases' h5 with b h5
  -- make the `b` in `h5` a variable
  rw [h5, h4 ] at h1
  -- substitute the equalities established in `h4` and `h5` into `h1`
  rw [mul_comm w a, mul_comm w b] at h1
  -- swap the order of multiplied terms to required format
  rw [← add_mul] at h1
  -- factorise out `w`
  rw [mul_comm (a + b) w] at h1
  -- swap the order of multiplied terms to required format
  exact Dvd.intro (a + b) h1
  done

-- Lemma : if `p * r + a * t = 1` then for all `b`, `p * (x * b) + a * b * y = b`
lemma Multiply_Lemma {p a : ℤ} (h1: ∃ r t : ℤ , p * r + a * t = 1) :
    ∀ b : ℤ , ∃ x y : ℤ, p * (x * b) + a * b * y = b := by
  intro b
  rcases h1 with ⟨r, t, h2⟩
  use r
  use t
  -- unpack the quantifiers in `h1`
  apply_fun (· * b) at h2
  -- multiply through by `b`
  rw [mul_comm, Distrib.left_distrib, mul_comm, mul_comm b (a * t), one_mul] at h2
  rw [mul_assoc p r b, mul_assoc a t b, mul_comm t b] at h2
  rw [mul_assoc a b t]
  -- rewrites to obtain the goal and `h2` is the same form
  exact h2
  done

-- # Section II: Lemmas which are non-trivial and used in the main result

/- Lemma [Bezouts identity] : for integers `a`, `b` and `d`, such that `d` is the greatest common
divisor of `a` and `b`, there exist integers `x` and `y` such that `a * x + b * y = d` holds -/
lemma Bezouts_identity {a b d : ℤ} (h: gcd a b = d) : ∃ x y : ℤ , a * x + b * y = d := by
  use a.gcdA b, a.gcdB b
  rw [← h, ← Int.gcd_eq_gcd_ab a b, Int.coe_gcd]
  done

/- Lemma [Euclid's Lemma] : for integers `a`, `b` and `p`, where `p` is prime, if `p` divides`
`a * b` but does not divide `a`, then `p` divides `b` -/
lemma Euclids_lemma {p a b : ℤ} (h1 : p ∣ a * b) (h2 : Prime p ) (hp : 0 < p)
  (h3 : ¬ p ∣ a) : p ∣ b := by
  have h4 : gcd p a = 1 := Simple_GCD_lemma_2 hp h3 h2
  -- as `p` is a prime that does not divide `a`, `gcd p a` must be `1`
  have h5a : ∃ x y : ℤ , p * x + a * y = 1 := Bezouts_identity h4
  /- establish the existence of some x and y satisfying `p * x + a * y = 1` by applying Bezouts
  identity with `gcd p a = 1` from `h4` -/
  have h5 : ∀ d : ℤ, ∃ x y : ℤ , p * (x * d) + a * d * y  = d := Multiply_Lemma h5a
  /- establish the existence of some x and y satisfying `p * x + a * y = 1` by applying Bezouts
  identity with `gcd p a = 1` from `h4` ; multiply through by integer `d` to get `h5`-/
  have h6 : p ∣ p := by trivial
  have h7 : ∀ x1 : ℤ , p ∣ p * (x1 * b) := by
    intro x1
    exact h6.mul_right (x1 * b)
  have h8 : ∀ y1 : ℤ , p ∣ a * b * y1 := by
    intro y1
    exact h1.mul_right y1
  /- `h7` and `h8` establish that `p` divides `p * (x * b)` and `a * b * y` (using `h1 : p ∣ a * b`)
   Note `x1` and `y1` are used to distinguish to the later specialisation to `x` and `y` -/
  -- ''substitute'' in `b` as the general integer `d` in `h5`
  rcases h5 b with ⟨x, y, h5⟩
  -- unpack x and y in `h5`
  specialize h7 x
  specialize h8 y
  -- use the `x` and `y` in `h7` and `h8`, respectively
  exact Divide_Sum_Lemma h5 h7 h8
  -- `h5`, `h7` and `h8` are exactly in the form to show `p ∣ b` by `Divide_Sum_Lemma`
  done

/- Lemma [Euclid's Lemma, alternative presentation] : for integers `a`, `b` and `p`,
where `p` is prime, if `p` divides `a * b` then `p` divides `a` or `p` divides `b` -/
theorem Euclids_lemma_alternative {p a b : ℤ} (h1 : p ∣ a * b) (h2 : Prime p)
    (hp : 0 < p) :
    p ∣ a ∨ p ∣ b := by
  have h3 : ¬ p ∣ a → p ∣ b := Euclids_lemma h1 h2 hp
  by_contra! -- the ! makes it do simplifications too
  tauto
  -- tauto is meant to solve propositional logic goals: it's more specific but sometimes faster
  done


-- # Section III: Main result

/- Theorem : a semi-prime q1*q2 cannot be factored as p1 * p2 where p1 is prime and
not equal to either q1 or q2 -/
theorem Semi_Primes_Unique_Factorisation {q1 q2 p c : ℤ} (h1 : Prime p)
    (h2 : Prime q1) (h3 : Prime q2) (hq2 : 0 < q2) (h4 : p ≠ q1) (h5 : p ≠ q2)
    (hp : 0 < p) (hq1 : 0 < q1) :
    p * c ≠ q1 * q2 := by
  intro h6
  -- Rather than proving an inequality, we assume equality and prove false
  have h7 : (p ∣ (p * c)) := by norm_num
  rw [h6] at h7
  -- establish that `p` divides `q1 * q2`
  have h8: (p ∣ q1 ∨ p ∣ q2)  := Euclids_lemma_alternative h7 h1 hp
  -- by Euclid's lemma, as `p` is prime it divides `q1` or `q2`
  cases' h8 with h9 h10
  -- take each possibility of `p` dividing `q1` or `q2` in turn
  · have h11 : gcd p q1 = 1 :=  Primes_are_Coprime hp hq1 h1 h2 h4
    have h12 : p ≠ 1 := Prime.ne_one h1
    have h13 : gcd p q1 = p := Simple_GCD_lemma_1 hp h9
    -- we are dealing with the case where `p` divides `q1`
    aesop
    -- `h11`, `h12` and `h13` are together contradictory
    done
  · have h14 : gcd p q2 = 1 := Primes_are_Coprime hp hq2 h1 h3 h5
    have h15 : p ≠ 1 := Prime.ne_one h1
    have h16 : gcd p q2 = p := Simple_GCD_lemma_1 hp h10
    -- we are dealing with the case where `p` divides `q2`
    aesop
    -- `h14`, `h15` and `h16` are together contradictory
    done
  done
