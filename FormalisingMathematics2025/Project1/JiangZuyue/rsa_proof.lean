import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Prime.Basic


-- helper lemmas
variable (a b n : ℕ)
lemma mod_converter (ha: a % n = b): a ≡ b [MOD n] := by
  rw [← ha]
  apply Nat.ModEq.symm
  exact Nat.mod_modEq a n

lemma lemma1 : ((a % n) ^ b) % n = (a ^ b) % n := by
  change (a % n) ^ b ≡ (a ^ b) [MOD n] -- (a % n) ^ b ≡ a ^ b [MOD n]
  apply Nat.ModEq.pow
  exact Nat.mod_modEq _ _

lemma lemma2 : (a * b) % n = ((a % n) * (b % n)) % n := by
  change (a * b) ≡  a % n * (b % n) [MOD n]
  apply Nat.ModEq.mul
  apply Nat.ModEq.symm
  exact Nat.mod_modEq _ _
  apply Nat.ModEq.symm
  exact Nat.mod_modEq _ _

variable (p q n : ℕ)

lemma lemma3 (h : p ≡ 1 [MOD n]) (hn : 0 < n) (hp : 1 ≤ p)
    : ∃ k : ℕ, p = 1 + k * n := by
  -- convert modulo to |
  have h_symm : 1 ≡ p [MOD n] := by
    exact Nat.ModEq.symm h
  rw [Nat.modEq_iff_dvd'] at h_symm
  use (p - 1) / n
  rw [Nat.mul_comm, ← Nat.mul_div_assoc, Nat.mul_div_cancel_left]
  -- prove and rewrite p = 1 + (p - 1)
  have h1 : p = 1 + (p - 1) := by
    rw [← Nat.add_sub_assoc hp, Nat.add_comm]
    rfl
  nth_rewrite 1 [h1]
  rfl
  -- apply conditions
  exact hn
  exact h_symm
  exact hp

theorem lemma4 (m k p q : ℕ) -- Chinese Remainder Theorem
    (prime_p : Nat.Prime p)
    (prime_q : Nat.Prime q)
    (diff_pq : p ≠ q)
    (coprime_m_p : Nat.Coprime m p)
    (coprime_m_q : Nat.Coprime m q) :
    m ^ (k * (p-1) * (q-1)) % (p * q) = 1 := by
  -- Step 0: Prove that pq>1
  have h0 : 1 < p * q := by
    -- Since p and q are N, they are greater than 0
    have hp0 : 0 < p := Nat.Prime.pos prime_p
    have hq0 : 0 < q := Nat.Prime.pos prime_q
    -- Since p and q are prime, they are greater than 1
    have hp1 : 1 < p := Nat.Prime.one_lt prime_p
    -- The product of two numbers greater than 1 is greater than 1
    have hprod : 1 < p * q := by
      apply Nat.one_lt_mul_iff.mpr
      exact ⟨hp0, hq0, Or.inl hp1⟩
    exact hprod

  -- Step 1: Fermat's Little Theorem applied to p
  have h1 : m ^ (p-1) % p = 1 := by
    rw [← Nat.totient_prime prime_p]
    have : m ^ p.totient ≡ 1 [MOD p] := Nat.ModEq.pow_totient coprime_m_p
    apply Nat.ModEq.symm at this
    rw [← this]
    exact Nat.mod_eq_of_lt (Nat.Prime.one_lt prime_p)

  -- Step 2: Fermat's Little Theorem applied to q
  have h2 : m ^ (q-1) % q = 1 := by
    rw [← Nat.totient_prime prime_q]
    have : m ^ q.totient ≡ 1 [MOD q] := Nat.ModEq.pow_totient coprime_m_q
    apply Nat.ModEq.symm at this
    rw[← this]
    exact Nat.mod_eq_of_lt (Nat.Prime.one_lt prime_q)

  -- -- Step 3: Handle powers of (p-1)(q-1) mod p and q
  have h3 : m ^ ((p-1) * (q-1)) % p = 1 := by
    -- Nat.pow_mod:  a ^ b % n = (a % n) ^ b % n
    rw [Nat.pow_mul, Nat.pow_mod]
    rw [h1]
    simp
    exact Nat.mod_eq_of_lt (Nat.Prime.one_lt prime_p)

  have h4 : m ^ ((p-1) * (q-1)) % q = 1 := by
    -- change to m ^ ((q-1) * (p-1)) % q
    rw [Nat.mul_comm, Nat.pow_mul, Nat.pow_mod]
    rw [h2]
    simp
    exact Nat.mod_eq_of_lt (Nat.Prime.one_lt prime_q)

  -- Step 4: Extend to k multiples
  have h5 : m ^ (k * (p-1) * (q-1)) % p = 1 := by
    rw [Nat.mul_right_comm, Nat.mul_assoc, Nat.mul_comm]
    rw [Nat.pow_mul, Nat.mul_comm]
    rw [Nat.pow_mod]
    rw [h3]
    simp
    exact Nat.mod_eq_of_lt (Nat.Prime.one_lt prime_p)

  have h5':  m ^ (k * (p-1) * (q-1)) ≡ 1 [MOD p] := by
    apply mod_converter
    exact h5

  have h6 : m ^ (k * (p-1) * (q-1)) % q = 1 := by
    rw [Nat.mul_right_comm, Nat.mul_assoc, Nat.mul_comm]
    rw [Nat.pow_mul]
    rw [Nat.pow_mod, Nat.mul_comm]
    rw [h4]
    simp
    exact Nat.mod_eq_of_lt (Nat.Prime.one_lt prime_q)

  have h6':  m ^ (k * (p-1) * (q-1)) ≡ 1 [MOD q] := by
    apply mod_converter
    exact h6

  have h5h6 : (m ^ (k * (p-1) * (q-1)) ≡ 1 [MOD p]) ∧ (m ^ (k * (p-1) * (q-1)) ≡ 1 [MOD q]) := by
    exact ⟨h5', h6'⟩

  -- Step 5: Use CRT to combine the results modulo p and q
  have hmn : p.Coprime q := by
    exact (Nat.coprime_primes prime_p prime_q).mpr diff_pq

  have h7 : m ^ (k * (p - 1) * (q - 1)) ≡ 1 [MOD p * q] := by
    exact (Nat.modEq_and_modEq_iff_modEq_mul hmn).mp h5h6

  exact Nat.mod_eq_of_modEq h7 h0


-- rsa utils:
  -- m: message
  -- pb: public key
  -- pv: private key
  -- p, q: prime numbers
variable (m pb pv p q : ℕ)
/-- rsa encryption-/
def enc: ℕ := (m ^ pb) % (p * q)
/-- rsa decryption-/
def dec (enc: ℕ): ℕ := (enc ^ pv) % (p * q)


-- rsa correctness: dec(enc(m)) = m
theorem rsa_correctness (prime_p: Nat.Prime p) (prime_q: Nat.Prime q)
    (diff_pq : p ≠ q) (coprime_m_p : Nat.Coprime m p)
    (coprime_m_q : Nat.Coprime m q)
    (one_lt_pub_e : 1 < pb)
    (one_lt_priv_e : 1 < pv)
    (msg_lt_pq : m < (p * q))
  -- (pub_e_lt_totient : pb < (p * q).totient)
    (pub_e_coprime_totient : pb * pv ≡ 1 [MOD (p-1)*(q-1)])
    : dec pv p q (enc m pb p q) = m := by
  rw [enc, dec]
  rw [lemma1, ← pow_mul]
  -- pb * pv = 1 + k * (p-1) * (q-1) by lemma3
  let e := pb * pv
  have hphi_n : 0 < (p-1) * (q-1) :=
    Nat.mul_pos (Nat.sub_pos_of_lt prime_p.one_lt) (Nat.sub_pos_of_lt prime_q.one_lt)
  have he : 1 ≤ e := by
    apply Nat.one_le_of_lt
    exact Nat.mul_pos (Nat.lt_of_succ_lt one_lt_pub_e) (Nat.lt_of_succ_lt one_lt_priv_e)
  obtain ⟨k, hk⟩ := lemma3 e ((p-1) * (q-1)) pub_e_coprime_totient hphi_n he

  -- Replace pb * pv using its equivalent expression
  have hk' : pb * pv = 1 + k * ((p-1) * (q-1)) := by
    rw [← hk]
  rw [hk', pow_add, ← mul_assoc]
  -- Distribute exponentiation: m ^ (1 + k * (p-1)*(q-1)) % (p*q)
  rw [lemma2]
  -- m ^ 1 % (p*q) = m % (p*q)
  rw [lemma4 m k p q prime_p prime_q diff_pq]
  simp
  exact Nat.mod_eq_of_lt msg_lt_pq
  exact coprime_m_p
  exact coprime_m_q
