import Mathlib.Tactic
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Span.Defs

open Set Submodule

open scoped Classical

set_option autoImplicit true

/-
steinitz exchange lemma for X ⊆ V a vector space over field K
if 1. u ∈ Span X, 2. v ∈ X, 3. u ∉ Span (X \ {v}), 4. Y = (X \ {v}) ∪ {u}
then Span X = Span Y
-/

-- definition of vector space from
-- "https://leanprover-community.github.io/mathematics_in_lean/C09_Linear_Algebra.html"
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  (v u : V) (X : Set V)

-- key lemma that makes the proof work, encodes the "exchange property"
lemma v_lin_comb (hu_in : u ∈ span K X) (hv : v ∈ X) (hu_n_in : u ∉ span K (X \ {v})) :
    ∃ (c : V) (α : K), α ≠ 0 ∧ c ∈ span K (X \ {v}) ∧ u = c + α • v := by
  -- quite the pedantic assertion, but i guess it is necessary, maybe there is a better way
  have hX_split : X = (X \ {v}) ∪ {v} := by
    -- special thanks to David Ang and Kevin Buzzard for clearing up the need for this
    rw [diff_union_self, union_comm, singleton_union, insert_eq_of_mem hv]
  -- split X into two parts, X \ {v} and {v} so that we can represent
  -- it as a linear combination of the two parts
  rw [hX_split, span_union, mem_sup] at hu_in
  -- extract these vectors
  rcases hu_in with ⟨c, hc, d, hd, hcdu⟩
  -- extract the coefficient of v
  rw [mem_span_singleton] at hd
  -- substitute the coefficient of v into the linear combination
  rcases hd with ⟨α, rfl⟩
  -- use witnesses
  use c, α

  -- we need to show that α is not 0
  have hαn0 : α ≠ 0 := by
    by_contra h
    rw [h, zero_smul, add_zero, eq_comm] at hcdu
    rw [hcdu] at hu_n_in
    contradiction

  exact ⟨hαn0, hc, eq_comm.mp hcdu⟩ -- add proofs of c ∈ span K (X \ {v}) and u = c + α • v

theorem steinitz_exchange (hu_in : u ∈ span K X) (hv : v ∈ X) (hu_n_in : u ∉ span K (X \ {v}))
    (hY : Y = ((X \ {v}) ∪ {u})) : span K X = span K Y := by
  /-
  as Span X = Span Y ↔ Span X ⊆ Span Y ∧ Span Y ⊆ Span X ↔ X ⊆ Span Y ∧ Y ⊆ Span X we rw
  and deal with each goal separately, we also break down the definition of subset
  -/
  rw [span_eq_span] <;> rw [subset_def]

  · simp only [SetLike.mem_coe]
    /-
    Case 1: Span X ⊆ Span Y ↔ X ⊆ Span Y
    We assume x is in X and show it is in Span Y by breaking down into two cases:
    a) x ∈ X \ {v} and b) x ∈ {v}

    special thanks to Bhavik and Dirichlet @thedirichlet for the suggestion to use
    simp to convert ↑X to Xs
    -/
    intro x hx -- assume x is in X and break down Y into its parts
    rw [hY]

    /- chnage hx : x ∈ X to hx : x ∈ X \ {v} ∨ x = v
    has to be a better way to do this, its kind of simple -/
    have hX_split : X = (X \ {v}) ∪ {v} := (Set.diff_union_of_subset (by simpa)).symm

    rw [hX_split] at hx

    cases hx with
    | inl h =>
      -- Case 1a) x ∈ X \ {v}
      -- x ∈ X \ {v} → x ∈ Span (X \ {v}) trivially
      have hx_span : x ∈ span K (X \ {v}) :=
        subset_span h
      -- we can show that X \ {v} ⊆ (X \ {v}) ∪ {u}
      have hX_diff_subset_Y : X \ {v} ⊆ (X \ {v}) ∪ {u} := subset_union_left
      -- we can now use the monotonicity of span to close the goal
      exact span_mono hX_diff_subset_Y hx_span

    | inr h =>
      -- Case 1b) x ∈ {v} ↔ x = v
      -- need to get it into the form where i can apply v_linear_comb
      rw [mem_singleton_iff] at h
      rw [span_union, mem_sup, h]
      -- now the goal is a lot like what the lemma tells us so we use it
      obtain ⟨c, α, hα, hc, hu_eq_cav⟩ :
          ∃ (c : V) (α : K), α ≠ 0 ∧ c ∈ span K (X \ {v}) ∧ u = c + α • v :=
        v_lin_comb v u X hu_in hv hu_n_in
        -- help from kind xena users: Ben @undefined2338 and Dirichlet @thedirichlet

      -- create witnesses to close the goal
      let y' := -(1/α) • c
      let z' := (1/α) • u

      have hy_in : y' ∈ span K (X \ {v}) := smul_mem _ _ hc

      have hz_in : z' ∈ span K {u} := by
        rw [mem_span_singleton]
        use 1 / α

      use y', hy_in, z', hz_in
      -- simple calculation to close the goal
      calc
        y' + z' = -(1/α) • c + (1/α) • u := by dsimp [y', z']
        _ = -(1/α) • c + (1/α) • (c + α • v) := by rw [hu_eq_cav]
        _ = -(1/α) • c + (1/α) • c + (1/α) • α • v := by simp
        _ = α⁻¹ • α • v := by simp
        _ = v := by rw [smul_smul, mul_comm, Field.mul_inv_cancel, one_smul]; exact hα

  · simp
    /-
    Case 2: Span Y ⊆ Span X ↔ Y ⊆ Span X
    We assume y is in Y and show it is in Span X by again breaking down into two cases:
    a) y ∈ X \ {v} and b) y ∈ {u}
    -/
    -- we assume y is in Y with the goal of showing it is in Span X
    intro y hy
    -- break down the definition of Y to X \ {v} ∪ {u}
    rw [hY, mem_union] at hy

    -- split into cases y ∈ X \ {v} and y = u and show y ∈ Span X
    cases hy with
    | inl h =>
      -- Case 2a) y ∈ X \ {v}
      rw [mem_diff_singleton] at h
      -- i have y ∈ X and i want to go from y ∈ X to y ∈ Span X so i use subset_span
      exact subset_span h.left
    | inr h =>
      -- Case 2b) y ∈ {u}
      -- y ∈ {u} → y = u and u in X by assumption
      rw [mem_singleton_iff] at h
      rw [h]
      exact hu_in

-- BM: I added α ≠ 0 and v ∈ Y to this lemma, I think they're both needed.
-- If `α = 0`, then the RHS is too small (take Y a basis of V \ span {v}, that should give a
-- counterexample)
-- If `v ∉ Y` then it might not be in the LHS but it will be in the RHS (same counterexample I
-- think).

lemma span_replaced_scal_mul (Y : Set V) (hY_fin : Y.Finite) (α : K) (v : V) (hα : α ≠ 0)
    (hvnot0 : v ≠ 0) (hvmem : v ∈ Y) :
    span K Y = span K (Y \ {v} ∪ {α • v}) := by
  rw [span_eq_span]
  · intro y hy
    simp only [union_singleton, SetLike.mem_coe]
    obtain rfl | hyv := eq_or_ne y v
    · have : α • y ∈ span K (insert (α • y) (Y \ {y})) := subset_span (by simp)
      rwa [smul_mem_iff _ hα] at this
    · apply subset_span
      simp [hyv, hy]
  · simp only [union_singleton, insert_subset_iff, SetLike.mem_coe, diff_singleton_subset_iff]
    constructor
    · exact smul_mem (span K Y) α (subset_span hvmem)
    · intro y hy
      exact mem_insert_of_mem _ (subset_span hy)

-- BM: I added the assumption hY_fin here to prove it. I'm pretty certain that assumptoin is needed,
-- as otherwise you could have Y = V (formally speaking, Y = Set.univ), and then no choice of α
-- can work
variable [Infinite K]
lemma exists_scal_mul (hX_fin : X.Finite) (Y : Set V) (hY_fin : Y.Finite) (x : V) (hxnot0 : x ≠ 0) :
    ∃ α : K, α ≠ 1 ∧ (α • x ∉ X) ∧ (α • x ∉ Y) := by
  have : (insert (1 : K) ((· • x) ⁻¹' (X ∪ Y))).Finite :=
    ((hX_fin.union hY_fin).preimage (smul_left_injective K hxnot0).injOn).insert 1
  obtain ⟨α, hα⟩ := this.infinite_compl.nonempty
  use α
  simpa using hα

lemma induction_step_left (hv_n_in : v ∉ X) (hX_fin : X.Finite) (Y' : Set V)
    (hY'_fin : Y'.Finite) (h_span_eq : span K X = span K Y') (h_inter_empty : X ∩ Y' = ∅)
    (h : span K (insert v X) ≤ span K Y') (hvnot0 : v ≠ 0):
    (∃ Y, Y.Finite ∧ span K (insert v X) = span K Y ∧ insert v X ∩ Y = ∅) := by

  -- case Span insert v X ⊆ Span Y'
  -- first show that Span insert v X = Span X = Span Y'
  have h_span_vXeqY' : span K (insert v X) = span K Y' := by
    rw [span_le, ← h_span_eq] at h
    -- I go from insert v X ⊆ ↑(span K X) to span K (insert v X) ⊆ ↑(span K X)
    -- and then from span K (insert v X) ⊆ ↑(span K X) to span K (insert v X) = span K X
    -- then I use h_span_eq to close the goal
    rw [← h_span_eq]
    apply le_antisymm
    · rwa [span_le]
    · exact span_mono (subset_insert _ _)

  -- use the exists_scal_mul lemma to get a scalar α such that α • v ∉ Y'
  obtain ⟨α, hα_neq, hα_ninY', hα_ninX⟩ : ∃ α : K, α ≠ 1 ∧ α • v ∉ Y' ∧ α • v ∉ X :=
    exists_scal_mul Y' hY'_fin X hX_fin v hvnot0

  -- create witness
  let u := α • v
  -- show using v ≠ 0 and a ≠ 1 so v ≠ α • v
  have h_vu_disjoint : Disjoint ({v} : Set V) {α • v} := by sorry
  let Y := (Y' \ {v}) ∪ {α • v}

  -- prove that Y is finite
  have hY_fin : ((Y' \ {v}) ∪ {α • v}).Finite :=
    Finite.union (Finite.diff hY'_fin _) (finite_singleton u) -- BM: changed

  -- prove that Span Y' = Span Y
  have h_span_YeqY' : span K Y' = span K Y := by
    exact span_replaced_scal_mul Y' hY'_fin α v sorry hvnot0 sorry
    -- BM: first one looks like a missing assumption
    -- second one I didn't think about properly
  have h_span_vXeqY : span K (insert v X) = span K Y :=
    h_span_vXeqY'.trans h_span_YeqY' -- suggested by Fangming Li

  -- prove that X ∩ Y = ∅
  -- BM: a more common way of writing this is Disjoint X Y
  have hvXintY : insert v X ∩ Y = ∅ := by
    rw [insert_eq, union_inter_distrib_right]
    rw [inter_union_distrib_left, inter_union_distrib_left, diff_eq_compl_inter]
    rw [← inter_assoc, inter_compl_self, empty_inter, empty_union]
    rw [Disjoint.inter_eq h_vu_disjoint, empty_union]
    rw [inter_singleton_eq_empty.mpr hα_ninX, union_empty]
    rw [← inter_assoc, inter_eq_left.mpr (Set.subset_compl_singleton_iff.mpr hv_n_in)]
    exact h_inter_empty

  use Y

lemma induction_step_right (hv_n_in : v ∉ X) (hX_fin : X.Finite) (Y' : Set V)
    (hY'_fin : Y'.Finite) (h_span_eq : span K X = span K Y') (h_inter_empty : X ∩ Y' = ∅)
    (h : ¬span K (insert v X) ≤ span K Y') (hvnot0 : v ≠ 0):
    ∃ Y, Y.Finite ∧ span K (insert v X) = span K Y ∧ insert v X ∩ Y = ∅ := by
  -- case Span X ⊈ Span Y'
  -- first step is to show that there exists a vector u ∈ Span X ∪ {v} such that u ∉ Span X
  rw [span_le, subset_def, ← h_span_eq] at h
  push_neg at h
  rcases h with ⟨u, hu_in, hu_nin⟩
  simp at hu_nin
  apply @subset_span K at hu_in
  simp at hu_in
  /-
  at this point I have shown kind of u ∈ span K (insert v X) and u ∉ span K X
  which is not exactly what I need because the arguments of steinitz exchange lemma
  are a proof of u ∈ Span insert v X and u ∉ Span (insert v X \ {v})
  so first i prepare an intermediate set Z = insert v X and the right hypotheses for it
  -/
  let Z := insert v X
  let W := (Z \ {v} ∪ {u})
  have hW : W = (Z \ {v} ∪ {u}) := rfl
  have hu_inZ : u ∈ span K Z := hu_in
  have hu_ninZv : u ∉ span K (Z \ {v}) := by sorry
  have hZ_eq : Z \ {v} = X := by sorry
  have hv_in : v ∈ Z := mem_insert v X

  have h_span_XeqY : span K Z = span K (Z \ {v} ∪ {u}) := by
    exact @steinitz_exchange K _ V _ _ v u _ _ hu_inZ hv_in hu_ninZv hW

  /-
  after using steinitz exchange lemma, we have shown that
  span K (insert v X) = span K (insert u (X \ {v}))
  so insert u (X \ {v}) is a good candidate for Y except that u might be in X
  so we need to replace u with a vector that is not in X using the exists_scal_mul lemma
  calling this new vector α • u = w we have to show that
  span K (insert u (X \ {v})) = span K (insert w (X \ {v}))
  which can be done using the span_replaced_scal_mul lemma
  -/
  obtain ⟨α, hα_neq, hα_nin⟩ : ∃ α : K, α ≠ 1 ∧ α • u ∉ X := by
    sorry

  let Y := (Z \ {v} ∪ {α • u})

  have hY_fin : (Z \ {v} ∪ {α • u}).Finite := by
    rw [hZ_eq]
    exact Finite.union hX_fin (finite_singleton (α • u))
  have hSXveqSY : span K (insert v X) = span K Y := by sorry
  have hvXintY : (insert v X) ∩ Y = ∅ := by sorry

  use Y -- once, infoview complained about no exact closing the goal but since then it was okay

lemma induction_step (v : V) (X : Set V) (hv_n_in : v ∉ X) (hX_fin : X.Finite)
    (hk : ∃ Y : Set V, Y.Finite ∧ span K X = span K Y ∧ X ∩ Y = ∅) (hvnot0 : v ≠ 0) :
    (∃ Y : Set V, Y.Finite ∧ span K (insert v X) = span K Y ∧ (insert v X) ∩ Y = ∅) := by
  -- extracting the witnesses from hk
  rcases hk with ⟨Y', hY'_fin, h_span_eq, h_inter_empty⟩

  -- splitting into cases Span X ⊆ Span Y and Span X ⊈ Span Y
  have hX_in_Y' : span K (insert v X) ≤ span K Y' ∨ ¬ span K (insert v X) ≤ span K Y' :=
    em (span K (insert v X) ≤ span K Y')

  cases hX_in_Y' with
  | inl h =>
    exact @induction_step_left _ _ _ _ _ _ _ _ hv_n_in hX_fin Y' hY'_fin h_span_eq h_inter_empty h hvnot0
  | inr h =>
    exact @induction_step_right _ _ _ _ _ _ _ _ hv_n_in hX_fin Y' hY'_fin h_span_eq h_inter_empty h hvnot0


theorem replacement_thm (hX_fin : X.Finite) (h0notinX : 0 ∉ X) :
    ∃ Y : Set V, Y.Finite ∧ span K X = span K Y ∧ X ∩ Y = ∅ := by
  -- do induction on the finite set X
  have h_base : ∃ Y : Set V, Y.Finite ∧ span K ∅ = span K Y ∧ ∅ ∩ Y = ∅ := ⟨∅, by simp⟩

  induction X, hX_fin using Finite.dinduction_on with -- BM: changed
  | H0 =>
    exact h_base
  | @H1 a S ha hs ih =>
    have h0notinS : 0 ∉ S := by
      intro h
      apply h0notinX
      rw [mem_insert_iff]
      right
      exact h
    have ha_ne_0 : a ≠ 0 := by
      by_contra ha_eq_0
      rw [ha_eq_0, insert_eq, mem_union] at h0notinX
      tauto
    exact induction_step a S ha hs (ih h0notinS) ha_ne_0
