import Mathlib.Tactic
open Classical

-- Define the variables, I will be using injective maps between 3 spaces to prove theorem 2.33 in Principle of Mathematical Analysis
variable (X : Type) [MetricSpace X]
variable (Y : Type) [MetricSpace Y]
variable (K : Type)

variable (fyx : Y → X) (hyx1: Continuous fyx)(hyx2: Function.Injective fyx)(hyx3: IsOpenMap fyx)
variable (fky : K → Y) (hky2: Function.Injective fky)

omit [MetricSpace Y] in
/--Theorem 2.30: Suppose Y ⊆ X. A subset E of Y is open relative to Y if and only if
there exists an open subset G of X such that E = Y ∩ G.-/
theorem subset_open_iff_inter_open_l (ι : Type) (V : ι → Set X)
    (hV : ∀i : ι, IsOpen (V i)) (hV'': ∀i : ι, (V i) ⊆ Set.range fyx):
    ∀ i : ι, ∃ G : Set X, IsOpen G ∧ V i = (Set.range fyx) ∩ G := by
  intro i
  specialize hV i
  specialize hV'' i
  rw [Metric.isOpen_iff] at hV
  choose ε hε using hV
  use (⋃ (p : X) (hp : p ∈ V i), Metric.ball p (ε p hp))
  constructor
  · apply isOpen_iUnion
    · intro xx
      · apply isOpen_iUnion
        · intro hxx
          exact Metric.isOpen_ball
  · ext x
    constructor
    · intro hx
      rw [Set.mem_inter_iff]
      constructor
      · exact hV'' hx
      · rw [Set.mem_iUnion]; use x
        rw [Set.mem_iUnion]; use hx
        specialize hε x hx
        obtain ⟨hε_1, hε_2⟩ := hε
        simp
        exact hε_1
    · intro hx
      obtain ⟨hx_1, hx_2⟩ := hx
      rw [Set.mem_iUnion] at hx_2
      obtain ⟨q, hq⟩ := hx_2
      rw [Set.mem_iUnion] at hq
      obtain ⟨hq, hqq⟩ := hq
      have h_op: Metric.ball q (ε q hq) ⊆ V i := by
        specialize hε q hq
        obtain ⟨_, hε⟩ := hε
        exact hε
      exact h_op hqq



include hyx3 hyx2 in
-- omit [MetricSpace K] in
/--Theorem 2.33 (→): Suppose K ⊆ Y ⊆ X.If K is compact relative to X, then K is compact relative to Y.-/
theorem compact_sub_rel_X_if_Y: IsCompact (Set.range (fyx ∘ fky)) → IsCompact (Set.range fky) := by
  classical
  intro h1
  rw [isCompact_iff_finite_subcover]
  intro ι U hU h2
  -- Because of the use of injective maps, will be using a set of image of U which is V to do the rest of the prove
  let V := ((fyx '' ·) ∘ U) -- The collection of opensets called V in the proof. Which is the open cover.
  -- Now I prove the correponding statements of V, similar to the ones with U.
  have hV: ∀i : ι, IsOpen (V i):= by
    intro i
    specialize hU i
    exact hyx3 (U i) hU
  have hV' : Set.range (fyx ∘ fky) ⊆ ⋃ i, V i := by
    intro x hx
    rw [Set.mem_iUnion]
    rw [Set.subset_def] at h2
    rw [Set.range] at hx
    simp only [Function.comp_apply, Set.mem_setOf_eq] at hx
    obtain ⟨y, hy⟩ := hx
    specialize h2 (fky y)
    simp only [Set.mem_range, exists_apply_eq_apply, Set.mem_iUnion, forall_const] at h2
    obtain ⟨i, hi⟩ := h2
    use i
    rw [← hy]
    use fky y

  have hV'': ∀i : ι, V i ⊆ Set.range fyx := by
    intro i x hx
    rw [Set.range]
    obtain ⟨x_1, ⟨hx_1_1, hx_1_2⟩⟩ := hx
    use x_1

  -- Use the theorem 2.30 with V and hVs.
  have h230 := subset_open_iff_inter_open_l X Y fyx ι V hV  hV''
  -- Choose G and hG from theorem.
  choose G hG using h230

  rw [isCompact_iff_finite_subcover] at h1
  have hG': ∀ (i : ι), IsOpen (G i) := by intro i; specialize hG i; obtain ⟨h3,_⟩:=hG; exact h3
  have hG'':Set.range (fyx ∘ fky) ⊆ ⋃ i, G i := by
    intro x hx
    specialize hV' hx
    rw [Set.mem_iUnion] at hV'
    obtain ⟨i, hi⟩ := hV'
    rw [Set.mem_iUnion]
    use i
    specialize hG i
    obtain ⟨_, hG⟩ := hG
    have hVG: V i ⊆ G i := by rw [hG]; simp
    apply hVG
    exact hi
  specialize h1 G hG' hG''
  obtain ⟨s, hs⟩ := h1
  have hKY: Set.range (fyx ∘ fky) ⊆ Set.range (fyx) := by
    intro x hx
    rw [Set.range] at hx
    rw [Set.range]
    simp only [Function.comp_apply, Set.mem_setOf_eq] at hx
    obtain ⟨y, hy⟩ := hx
    simp only [Set.mem_setOf_eq]
    use (fky y)
  have hfinal: Set.range (fyx ∘ fky) ⊆ ⋃ i ∈ s, V i := by
    intro x hx
    rw [Set.subset_def] at hs
    specialize hs x hx
    rw [Set.mem_iUnion] at hs
    obtain ⟨i, hi⟩ := hs
    rw [Set.mem_iUnion] at hi
    obtain ⟨hi', hi⟩ := hi
    rw [Set.mem_iUnion]
    specialize hG i
    obtain ⟨_, hG⟩ := hG
    use i
    rw [Set.mem_iUnion]
    use hi'
    rw [hG]
    constructor
    · exact hKY hx
    · exact hi

  use s
  intro y hy
  simp only [Set.mem_iUnion, exists_prop]
  rw [Set.subset_def] at hfinal
  specialize hfinal (fyx y)
  have h3: fyx y ∈ Set.range (fyx ∘ fky) := by
    simp only [Set.mem_range, Function.comp_apply]
    simp only [Set.mem_range] at hy
    obtain ⟨y_1,hy_1⟩:=hy
    use y_1
    rw [hy_1]
  specialize hfinal h3
  simp only [Set.mem_iUnion, exists_prop] at hfinal
  obtain ⟨i,⟨ hi_1,hi_2⟩ ⟩:=hfinal
  use i
  constructor
  · exact hi_1
  · obtain ⟨yy,⟨ hyy,hyy'⟩ ⟩:=hi_2
    rw [Function.Injective.eq_iff] at hyy'
    rw [← hyy']
    exact hyy
    exact hyx2



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
