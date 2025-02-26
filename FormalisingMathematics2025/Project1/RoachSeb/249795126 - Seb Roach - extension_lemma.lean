import Mathlib

universe u

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
-- This above defines a Vector Space V, group structure is important for later

set_option autoImplicit true
set_option relaxedAutoImplicit true

variable {ι : Type*}  -- Index set for the original vectors
variable (v' : Sum ι Unit → V) (v: ι → V)  -- Full family of vectors, including u
axiom v_subset_v' : ∀ i : ι, v i = v' (Sum.inl i)

example (u : Unit) : u = () := by
  rfl  -- Reflexivity proves this since Unit has only one element

variable (h_li : LinearIndependent K v) -- Assume v is linearly dependent

variable (h_ld : ¬ LinearIndependent K v') -- Assume v' is not

variable {α β : Type u}

inductive image_of (f : α → β) : β → Type u
 | imf (a : α) : image_of f (f a)
-- I think you didn't use this?

-- It's good to keep Lemmas general first with arbitrary variables
-- Yes!

lemma exists_nonzero_in_kernel (h : ¬ LinearIndependent K v'):
  ∃ l : (Sum ι Unit →₀ K), l ≠ 0 ∧ Finsupp.linearCombination K v' l = 0 := by
  rw [linearIndependent_iff_ker] at h
  rw [LinearMap.ker_eq_bot'] at h
  push_neg at h
  -- #check h -- don't keep #check in finished code
  obtain ⟨l, l_ne_zero, lin_comb_zero⟩ := h
  -- #check l
  exact ⟨l,lin_comb_zero, l_ne_zero⟩

lemma function_zero_on_sum
    (f : Sum A B →₀ K)
    (hA : ∀ a : A, f (Sum.inl a) = 0)
    (hB : ∀ b : B, f (Sum.inr b) = 0) :
    f = 0 := by
  apply Finsupp.ext
  intro x
  cases x with
  | inl a => exact hA a
  | inr b => exact hB b


lemma restriction_zero_implies_complement_nonzero
    (f : Sum A B →₀ K)
    (h_nonzero : f ≠ 0)
    (h_restrict_zero : ∀ b : B, f (Sum.inr b) = 0):
    ∃ a : A, f (Sum.inl a) ≠ 0 := by

  -- Assume for contradiction that f restricted to A is also zero
  by_contra h_contra
  -- #check h_contra
  push_neg at h_contra -- Now h_contra: ∀ a, f (Sum.inl a) = 0
  -- #check h_contra
  -- doing by_contra! does by_contra and push_neg together

  -- Show f must be zero everywhere
  have f_zero : f = 0 := function_zero_on_sum f h_contra h_restrict_zero

  -- Derive a contradiction with h_nonzero
  contradiction
  -- nice

#check v'



lemma lambda_nonzero
    (h_li : LinearIndependent K v)
    (l : Sum ι Unit →₀ K)
    (l_ne_zero : l ≠ 0)
    (lin_comb_zero : Finsupp.linearCombination K v' l = 0) :
    l (Sum.inr ()) ≠ 0 := by
  -- Don't leave errors in finished code; use sorry to indicate you haven't finished something
  -- Assume for contradiction that l is zero on Unit
  by_contra h_l_unit_zero
  -- Now h_l_unit_zero: l (Sum.inr unit) = 0

  -- Apply restriction_zero_implies_complement_nonzero
  have l_iota_nonzero :=
    restriction_zero_implies_complement_nonzero l l_ne_zero (λ _ => h_l_unit_zero)
  #check l_iota_nonzero

  obtain ⟨a, ha⟩ := l_iota_nonzero
  #check a
  #check ha
  #check Finsupp.linearCombination K v'

  let f : ι → Sum ι Unit := Sum.inl
  have hf : Function.Injective f := Sum.inl_injective
  let l' : ι → K := Finsupp.comapDomain f l (Function.Injective.injOn hf)
  have l'_eq_l : l' a = l (Sum.inl a) :=
    Finsupp.comapDomain_apply f l (Function.Injective.injOn hf) a
  have l'_nonzero : ∃ a, l' a ≠ 0 := by
    use a  -- Pick the same `a`
    rw [l'_eq_l]  -- Rewrite `l' a` in terms of `l`
    exact ha  -- Since `ha : l (Sum.inl a) ≠ 0`, we conclude `l' a ≠ 0`

  sorry
