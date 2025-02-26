import Mathlib.Tactic
open Classical

-- Define the variables, I will be using injective maps between 3 spaces to prove theorem 2.33 in
-- Principle of Mathematical Analysis
variable (X : Type) [MetricSpace X]
variable (Y : Type) [MetricSpace Y]
variable (K : Type)

variable (fyx : Y → X) (hyx1: Continuous fyx) (hyx2: Function.Injective fyx) (hyx3: IsOpenMap fyx)
variable (fky : K → Y) (hky2: Function.Injective fky)

omit [MetricSpace Y] in
/-- Theorem 2.30: Suppose Y ⊆ X. A subset E of Y is open relative to Y if and only if
there exists an open subset G of X such that E = Y ∩ G. -/
theorem subset_open_iff_inter_open_l (ι : Type) (V : ι → Set X)
    (hV : ∀i : ι, IsOpen (V i)) (hV'': ∀i : ι, V i ⊆ Set.range fyx):
    ∀ i : ι, ∃ G : Set X, IsOpen G ∧ V i = Set.range fyx ∩ G := by
  intro i
  specialize hV i
  specialize hV'' i
  rw [Metric.isOpen_iff] at hV
  choose ε hε_pos hε using hV
  use (⋃ (p : X) (hp : p ∈ V i), Metric.ball p (ε p hp))
  constructor
  · apply isOpen_iUnion -- BM: cdots aren't needed here since you only have one goal at a time
    intro xx
    apply isOpen_iUnion
    intro hxx
    exact Metric.isOpen_ball
  · ext x
    constructor
    · intro hx
      rw [Set.mem_inter_iff]
      constructor
      · exact hV'' hx
      · rw [Set.mem_iUnion]
        use x
        rw [Set.mem_iUnion]
        use hx
        simpa using hε_pos x hx
    · rintro ⟨hx_1, hx_2⟩
      rw [Set.mem_iUnion] at hx_2
      obtain ⟨q, hq⟩ := hx_2
      rw [Set.mem_iUnion] at hq
      obtain ⟨hq, hqq⟩ := hq
      exact hε q hq hqq

include hyx3 hyx2 in
/--
Theorem 2.33 (→): Suppose K ⊆ Y ⊆ X.If K is compact relative to X, then K is compact relative to
Y.
-/
theorem compact_sub_rel_X_if_Y (h1 : IsCompact (Set.range (fyx ∘ fky)) ) :
    IsCompact (Set.range fky) := by
  rw [isCompact_iff_finite_subcover]
  intro ι U hU h2
  -- Because of the use of injective maps, will be using a set of image of U which is V to do the
  -- rest of the proof
  let V : ι → Set X := (fyx '' ·) ∘ U
  -- The collection of opensets called V in the proof, which is the open cover.
  -- Now I prove the correponding statements of V, similar to the ones with U.
  have hV (i : ι) : IsOpen (V i) := hyx3 (U i) (hU i)
  have hV' : Set.range (fyx ∘ fky) ⊆ ⋃ i, V i := by
    rintro x ⟨y, rfl⟩
    rw [Set.mem_iUnion]
    simp only [Function.comp_apply, Set.mem_setOf_eq]
    rw [Set.range_subset_iff] at h2
    simp only [Set.mem_iUnion] at h2
    obtain ⟨i, hi⟩ := h2 y
    use i, fky y

  have hV'': ∀i : ι, V i ⊆ Set.range fyx := by
    intro i x hx
    obtain ⟨x_1, hx_1_1, hx_1_2⟩ := hx
    use x_1

  -- Use the theorem 2.30 with V and hVs.
  have h230 := subset_open_iff_inter_open_l X Y fyx ι V hV hV''
  -- Choose G and hG from theorem.
  choose G hG' hG₂ using h230

  rw [isCompact_iff_finite_subcover] at h1
  have hG'' : Set.range (fyx ∘ fky) ⊆ ⋃ i, G i := hV'.trans (Set.iUnion_mono (by simp [hG₂]))
  specialize h1 G hG' hG''
  obtain ⟨s, hs⟩ := h1
  have hKY : Set.range (fyx ∘ fky) ⊆ Set.range fyx := by simp [Set.range_subset_iff]
  have hfinal : Set.range (fyx ∘ fky) ⊆ ⋃ i ∈ s, V i := by
    simpa [hG₂, Set.range_subset_iff] using hs

  use s
  rw [Set.range_subset_iff]
  intro y
  simp only [Set.mem_iUnion, exists_prop]
  specialize hfinal ⟨y, rfl⟩
  simp only [Set.mem_iUnion, exists_prop] at hfinal
  obtain ⟨i, hi_1, yy, hyy, hyy'⟩ := hfinal
  use i, hi_1
  rwa [← hyx2 hyy']

-- BM: I stopped here.

include hyx1 hyx3 hyx2 in
/--Theorem 2.33 (←): Suppose K ⊆ Y ⊆ X. If K is compact relative to Y, then K is compact relative to X.-/
theorem compact_sub_rel_Y_if_X: IsCompact (Set.range fky) → IsCompact (Set.range (fyx ∘ fky)) := by
  intro h1
  rw [isCompact_iff_finite_subcover]
  intro ι G hG hG'
  rw [isCompact_iff_finite_subcover] at h1
  let V := fun i ↦ fyx⁻¹' ((G i) ∩ (fyx '' Set.univ))
  have hV : ∀ (i : ι), IsOpen (V i) := by
    intro i
    apply IsOpen.preimage
    · exact hyx1
    · apply IsOpen.inter
      exact hG i
      exact hyx3 Set.univ isOpen_univ
  have hV' : Set.range (fky) ⊆ ⋃ i, V i := by
    intro y hy
    rw [Set.mem_iUnion]
    rw [Set.subset_def] at hG'
    specialize hG' (fyx y)
    have hyg : fyx y ∈ Set.range (fyx ∘ fky) := by
      obtain ⟨y_1, hy_1⟩ := hy
      use y_1
      simp only [Function.comp_apply]
      rw [hy_1]
    specialize hG' hyg
    rw [Set.mem_iUnion] at hG'
    obtain ⟨i, hi⟩ := hG'
    use i
    rw [Set.mem_preimage]
    constructor
    · exact hi
    · rw [propext (Function.Injective.mem_set_image hyx2)]
      trivial
  specialize h1 V hV hV'
  obtain ⟨s, hs⟩ := h1
  use s
  intro x hx
  rw [Set.mem_iUnion]
  simp only [Set.mem_iUnion, exists_prop]
  rw [Set.subset_def] at hs
  simp only [Set.mem_range, Function.comp_apply] at hx
  obtain ⟨k, hk⟩ := hx
  specialize hs (fky k) (Set.mem_range_self k)
  rw [Set.mem_iUnion] at hs
  obtain ⟨i, hi⟩ := hs
  simp only [Set.mem_iUnion, exists_prop] at hi
  obtain ⟨hi_1, hi_2⟩ := hi
  use i
  constructor
  · exact hi_1
  · rw [@Set.mem_preimage, hk] at hi_2
    exact Set.mem_of_mem_inter_left hi_2
