/-
In this Lean file we formalise the proof of Bolzano--Weierstrass theorem for R.
-/

import Mathlib.Tactic

-- Definitions
def converge (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |t - a n| < ε

def bounded (a : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ n, |a n| ≤ M

def monotone (a : ℕ → ℝ) : Prop :=
  ∀ n, (a (n+1) ≤ a n) ∨ (a (n+1) ≥ a n) -- This definition isn't right!!!
  -- you probably want (∀ n, (a (n+1) ≤ a n)) ∨ (∀ n, (a (n+1) ≥ a n))
  -- it's also usually a good idea to avoid ≥ and use ≤ if you can, but that's a much more minor
  -- point

def peak (n : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ m > n, a m ≤ a n

-- These are not exactly definitions but only to make our lives easier
def hasMonoSubseq (a : ℕ → ℝ) : Prop :=
  ∃ I : ℕ → ℕ, (StrictMono I) ∧ (monotone (a ∘ I))

def hasConvSubseq (a : ℕ → ℝ) : Prop :=
  ∃ I : ℕ → ℕ, ∃ t : ℝ, (StrictMono I) ∧ (converge (a ∘ I) (t))

-- A sequence either has a infinite or finite numebr of peaks
lemma eitherInfOrFinPeaks (a : ℕ → ℝ) :
    (∃ I : ℕ → ℕ, (StrictMono I) ∧ (∀ n, peak (I n) a)) ∨
    (∃ N : ℕ, ∀ n ≥ N, ¬ peak n a) := by
  sorry

-- First of the two lemmas: Every sequence has a monotone subsequence
lemma everySeqHasMonoSubseq (a : ℕ → ℝ) :
    hasMonoSubseq a := by
  use id
  constructor
  · intro a b h
    exact h
  · intro n
    simp [le_total]
  -- because the definition is wrong, this is super easy to prove

  -- have h := eitherInfOrFinPeaks a
  -- -- Split into two cases
  -- cases h
  -- -- Infinite peaks --
  -- case inl h =>
  --   obtain ⟨I, hI⟩ := h
  --   use I
  --   constructor
  --   · exact hI.left
  --   · intro n
  --     left
  --     apply hI.right
  --     apply hI.left
  --     linarith
  -- -- Finite peaks
  -- case inr h =>
  --   obtain ⟨N, hN⟩ := h
  --   sorry

-- Second lemma: Every bounded monotone sequence converges
lemma boundedMonoSeqConv (a : ℕ → ℝ) (hb : bounded a) (hm : monotone a) :
  ∃ t : ℝ, converge a t := by
    -- WLOG suppose a is non-decreasing
    wlog hmi : ∀ m n, a m ≥ a n
    obtain ⟨M, hM⟩ := hb -- you have two goals at this point!!
    let s := {a n | n : ℕ}
    have hs : BddAbove s
    · use M
      intro x hx
      obtain ⟨n, rfl⟩ := hx
      have h2 : a n ≤ |a n|
      · apply le_abs_self (a n)
      linarith [hM n]

    let c := sSup s

    -- First show c is an upper bound
    have hc : ∀ x ∈ s, x ≤ c
    · intro x hx
      have h3 : IsLUB s c
      · apply Real.isLUB_sSup
        use a 1
        use 1
        exact hs
      -- here's how you could finish:
      exact h3.1 hx
      -- Please don't leave any errors in your submitted code.

    -- Now show the limit is c
    use c
    intro ε hε
    obtain ⟨B, hB⟩ : ∃ B, c - ε < a B := by
      by_contra h
      push_neg at h
      have hce : ∀ x ∈ s, x ≤ c - ε
      · intro x hx
        obtain ⟨n, hn⟩ := hx
        linarith [h n]
      have hco : c ≤ c - ε
      · sorry
      linarith
    use B
    intro n hn
    have hca : |c - a n| = c - a n
    · rw [abs_of_nonneg]
      sorry
    sorry
    sorry

-- Third lemma which makes life easier
lemma subSeqOfBoundedSeqIsBounded (a : ℕ → ℝ) (I : ℕ → ℕ) (hb : bounded a) :
    bounded (a ∘ I) := by
  obtain ⟨B, hB⟩ := hb
  use B
  intro n
  apply hB

-- The theorem
theorem BolzanoWeierstrass (a : ℕ → ℝ) (ha : bounded a) :
    hasConvSubseq a := by
  obtain ⟨I, hI⟩ := everySeqHasMonoSubseq a
  have h := subSeqOfBoundedSeqIsBounded a I ha
  obtain ⟨t, ht⟩ := boundedMonoSeqConv (a ∘ I) h hI.right
  use I, t
  constructor
  · exact hI.left
  · exact ht
