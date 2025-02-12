/- In this project I will use Lean to prove some interesting properties about
the greatest common divisor (GCD) between two natural numbers.
The GCD is a basic but very important tool in Number Theory. We said that
two natural numbers are coprime if their GCD is 1. Also, as a not-so-exciting application,
the GCD can be used to prove that √2 is not a rational number.-/

import Mathlib.Tactic
open Nat

/-I will mostly work on natural numbers.-/
variable (a b n d: ℕ )
variable (x y : ℤ )

/-Before defining the GCD, we will need to introduce the divisibility between two
natural numbers. -/

def divides (a b : ℕ) : Prop := ∃ (k : ℕ), a * k = b

/-Although we can still use the usual notation 'a | b', the proposition 'divides' could
be useful at some points. Also, it is easider to just type letters down.-/
example : a ∣ b ↔ divides a b := by
  rw[divides]
  constructor
  intro h
  cases h with
  | intro k hk => use k; rw[hk]

  intro h'
  rcases h' with ⟨k, hk⟩
  use k
  rw[hk]

/-We then define the common divisors and hence the GCD between two natural numbers.-/
def common_divisors (a b : ℕ) := {d | d ∣ a ∧ d ∣ b}

def gcd' (a b : ℕ) : Prop := ∀ e ∈ common_divisors a b, ∃ d ∈ common_divisors a b, e ≤ d

/-Since the GCD that we just defined has type Prop, it would be difficult to
give numerical computation. However, what we have defined might be useful to prove
non-computaional results.
To overcome the computational issue, we still have to use the tactic 'Nat.gcd' from Mathlib.-/

#eval Nat.gcd 15 18

/-We also need another definition of the GCD, namely gcd(a,b) = ax + by, for some x,y ∈ ℤ.-/
def gcd'' (a b : ℕ) : Prop := ∃ x y : ℤ, a * x + b * y = Nat.gcd a b

/-Unfortunately, we will not prove here that gcd' ↔ gcd'' because the latter proposition is obtained
from the Euclidean Algorithm, which is not so relevant to our project. -/
/-However, we can prove the relation between 'common_divisors' and 'gcd''.-/

example: n ∈ common_divisors a b → n ∣ Nat.gcd a b:= by
  rintro ⟨h1, h2⟩
  cases h1 with
  | intro a' ha => cases h2 with
    |intro b' hb => rw[ha, hb];sorry

/-By rw[ha,hb] we change gcd(a,b) into gcd(na',nb'), but we do not know how to bring n out
of the gcd. In the original proof I have used the Euclidean Algorithm, but I have not formalised
it here. I now realised that the EA is in fact very essential in my project-/

/-The reverse implication should also be true.-/

example: n ∣ Nat.gcd a b → n ∈ common_divisors a b:= by
  rintro ⟨k, hk⟩
  sorry
/-For this one I need the fact that the GCD itself divides a and b, but I have no idea how
to show it in Lean.-/

/-In Mathlib I have found that an iteration has been used instead of the EA. It consists of
three properties of the GCD, namely gcd(a,b) = gcd(b,a), gcd(a,b) = gcd(a-b,b) and
gcd(a,0) = a. I will now prove these properties.-/

example: Nat.gcd a b = Nat.gcd b a:= by
  rw[Nat.gcd_comm]

example: Nat.gcd a b = Nat.gcd (a-b) b:= by
  sorry
/-For this one I need the fact that the GCD divides both a and b, and hence divides
any linear combination of a and b. Unfortunately, I was not able to find a way to give
the Lean proof. -/

example: Nat.gcd a 0 = a:= by
  rw[Nat.gcd_zero_right]

/-More importantly, if the GCD of two natural numbers is 1, then these two numbers are
said to be coprime.-/

def coprime (a b : ℕ) : Prop := Nat.gcd a b = 1

/-The following theorem is a direct consequence of the definition of coprime.-/

theorem coprime_def: coprime a b ↔ ∀ d ∈ common_divisors a b, d = 1:= by
  constructor
  intro h
  intro d hd
  sorry
  intro h'
  sorry
/-I think that I have not clarified that 'Nat.gcd' gives the largest common divisor of a and b.
So it is a (serious) issue of mixing the definitions that I came up with those from Mathlib.-/

/-In the informal proof of √2 being irrational, we first assume that √2 is rational,
i.e. √2 = p / q, where p,q ∈ ℕ , q ≠ 0 and gcd(p,q)=1. For ease of manipulation, we will
modify the equality so that it becomes 2 * q * q = p * p. Since p and q are coprime
we must have 2 ∣ p. Then the equality becomes 2 * q * q = (2 * k) * (2 * k), where k is
another natural number.
By rearranging we get q * q = 2 * p * p. Again by coprimality we get 2 ∣ q, but 2 ∣ p
and 2 ∣ q implies that gcd(p,q)≠ 1, leading to a contradiction.-/

/-Since we have mentioned the prime numbers, I have found a useful theorem from Mathlib,
which helps us to prove 2∣ p if we know that 2 ∣ p² is true. -/

#check Nat.prime_two.dvd_mul

/-This theorem states that if 2∣ pq, then we either have 2∣ p or 2∣ q.
In our proof , we have assumed that gcd(p,q) = 1. Since ℕ is a UFD, we must have
2∣ p². This implies that 2∣ p or 2∣ p, but both of them will give the claim that we
desired.-/

theorem even_of_even_sqr {p : ℕ} (h : 2 ∣ p ^ 2) : 2 ∣ p := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

/- What this result shows is that the square of even numbers must also be even. We will
first deduce that p is even, then we will show that q is also even, meaning that 2 divides
gcd(p,q)=1. However, in natural numbers 1 is not divisible by 2, then we have achieved
the goal.-/

example {p q : ℕ} (coprime_pq : p.Coprime q) : p ^ 2 ≠ 2 * q ^ 2 := by
  intro sqr_eq
  have h1: 2 ∣ p := by
    apply even_of_even_sqr
    rw [sqr_eq]
    norm_num
    -- We first obtain p² from the even theorem, and then rewrite p² so that we get 2 dividing
    -- an even number, which clearly holds.
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp h1 -- Here we have started the 'descent'.
  have : 2 * (2 * k ^ 2) = 2 * q ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have h2: 2 * k ^ 2 = q ^ 2 :=
    Nat.mul_left_cancel (by norm_num) this -- Derived directly from line 139 by cancelling 2 on both sides.
  have : 2 ∣ q := by
    apply even_of_even_sqr
    rw [pow_two, Nat.prime_two.dvd_mul]
    sorry
    /-The difference between this part and the even theorem is that I do not know how
    to do the case without giving a name to 2∣ q².-/
  have : 2 ∣ p.gcd q := by
    sorry
  have : 2 ∣ 1 := by
    sorry
  norm_num at this
  /- This last few lines have shown exactly the same problem as what I struggled before.
  It means that I will have to understand deeply the logic behind Lean's proof, as well as
  practising the tactics.-/
