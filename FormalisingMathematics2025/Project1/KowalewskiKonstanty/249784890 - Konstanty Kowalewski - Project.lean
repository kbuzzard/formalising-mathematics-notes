import Mathlib

/-!
# Formalising Mathematics Project 1

Konstanty Kowalewski
CID: 06020618

## Split conformal prediction

Let X = ℝⁿ be feature space
and Y = ℝ be response space.
Let X x Y have law P,
and (Xᵢ, Yᵢ) ∼ P for all i.
Let 0 < α < 1 be "nominal error level"
Define "prediction band" as

C : X → subsets of Y

such that for new i.i.d. pair (Xnew, Ynew) ∼ P
we have that P(Ynew ∈ C(Xnew)) ≥ 1 - α.
There exists a trivial example:
let C(Xnew) = Y with prob 1-α and ∅ otherwise.
We want a "better" C, and this is the want of CP.
-/

set_option autoImplicit true

-- hard to state without measure theory, even with sorried statements
theorem scp (α : ℝ) (n : ℕ) (C : X → ℝ) (X Y : ℕ → ℝ) (P : Prop → ℝ)
  : P (Y n + 1 ≤ X n) ≥ 1 - α := sorry

/-!
## Simpler setting
-/

/-!
### Intermediate result for induction functions
-/

open Finset Classical Nat

noncomputable section

variable
  (n : ℕ)
  (s : ℕ → ℝ)

/-- indicator I{Sn > Sk} -/
def ind (s : ℕ → ℝ) (n : ℕ) (k : ℕ) : ℝ :=
  if s n > s k then 1 else 0

example
  -- assume partial order without loss of generality
  (h_non_inc : ∀ x, s x ≥ s (x + 1))
  : ∑ k in range (n-1), ind s n k = ∑ k in range n, ind s n k := by
  -- induction example from Section 8 Sheet 1
  induction' n with d hd
  · rfl
  · rw [sum_range_succ]
    -- simp can "expand" defs, from Section 2 Sheet 5
    simp [ind]
    apply h_non_inc
    -- didn't need hd, so induction is not a good fit

-- attempt 2 (Iio and Iic)

lemma ind_at_nn_is_0 : ∀ n, ind s n n = 0 := by
  simp [ind]

example : ∑ k < n, ind s n k = ∑ k ≤ n, ind s n k := by
  rw [← sum_Iio_add_eq_sum_Iic]
  rw [self_eq_add_right]
  rw [ind_at_nn_is_0]

-- attempt 3 (special notation)

/-- notation for indicator I{Sₙ > Sₖ} -/
notation l " ⟩ " r => (if l > r then 1 else 0)

lemma lt_sum_eq_le_sum : ∑ k < n, (s n ⟩ s k) = ∑ k ≤ n, (s n ⟩ s k) := by
  rw [← sum_Iio_add_eq_sum_Iic]
  rw [self_eq_add_right]
  simp

-- additional assumptions
variable
  {h_distinct : s i ≠ s j} -- i and j are inferred from s args
  (h_non_inc : s x ≥ s (x + 1))


/-!
### Intermediate result about quantile inequality

⌈(n+1)(1-α)⌉ ≤ n+1
-/

lemma
  α_mul_n_lt_n
  (α_le_1 : α < 1)
  : Nat.ceil (α * n) ≤ n := by
  rw [Nat.ceil_le]
  apply mul_le_of_le_one_of_le_of_nonneg -- thanks Bhavik Mehta
  · exact le_of_lt α_le_1 -- via `exact?`
  -- `exact?` fails at first because it expands to `↑n`
  -- but this can be fixed with a gap, thanks Bhavik Mehta
  · exact Preorder.le_refl _
  -- `aesop?` instead finds simp_all
  -- simp_all only [gt_iff_lt, le_refl]
  · exact Nat.cast_nonneg' n -- via `exact?`


/-!
## Measure-theoretic probability
-/

/-!
### Random variables
-/

open MeasureTheory ProbabilityTheory NNReal

variable
  {Ω : Type}
  [MeasureSpace Ω]
  {P : Measure Ω}
  [IsProbabilityMeasure P]

  -- family {Xᵢ : i ∈ ℝ} of i.i.d. real-valued random variables
  {X : ℝ → Ω → ℝ}
  (h_meas : Measurable (X i))
  (h_ident : IdentDistrib (X i) (X j))
  (h_indep : ∀ i ≠ j, IndepFun (X i) (X j))

#check pdf (X 0) P (P.map (X 10)) 0
#check uniformOn {1,2,3}
#check P[X 0.3211]
#check moment (X pi) 10
#check ∂P/∂P
#check X 0

example : ∀ x, pdf (X 0) P x ≥ 0 := by
  intro x
  -- found with `exact?`
  exact _root_.zero_le (pdf (X 0) P x)

/-!
### Exchangeability

We used i.i.d., but we need less.
Let Z = (Z_1, ..., Z_n) ∈ ℝⁿ
with joint density f.
Z is exchangeable iff
for a.e. z_1, ..., z_n ∈ Z
f(z_1, ..., z_n) = f(z_1', ..., z_n')
where ' is any permutation in Sₙ.
-/

variable
  -- default bind rule would say { fᵢ : ℝ → ℝ | i ≤ n }
  -- using parentheses to instead say f : ℝⁿ → ℝ (thanks Bhavik Mehta)
  {α : ℝ}
  {f : (Fin n → ℝ) → ℝ}

  -- finite permutation to define exchangeability, thanks Bhavik Mehta
  {σ : Equiv.Perm (Fin n)}
  ( f_symm : ∀ x, f (λ y ↦ x (σ y)) = f x )

/-!
### Distributions

Example of push-forward measure
to define a normal distribution.
-/

variable
  -- X₀ ∼ N(μ, σ)
  {μ : ℝ}
  {σ : ℝ≥0}
  {h_normal : P.map (X 0) = gaussianReal 0 1}

example : P.map (X 0) = gaussianReal 0 1 := by
  exact h_normal

#min_imports -- doesn't find probability sources :(

#lint
