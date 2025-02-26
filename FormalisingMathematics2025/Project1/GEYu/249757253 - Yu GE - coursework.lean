import Mathlib.Tactic
/-!
  # Basic Definitions and Helper Theorems
-/

variable (X : Type)
  (A B C D : Set X)
def TendsTo (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |x n - a| < ε

/-- Unfolding the definition of `TendsTo`. -/
theorem tendsTo_def {x : ℕ → ℝ} {a : ℝ} :
    TendsTo x a ↔ ∀ ε, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → |x n - a| < ε := by
  rfl

/-- The definition of subset in Lean. -/
theorem subset_def : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := by
  rfl

-- This proof is taken directly from the course notes.
/-- Uniqueness of limits for real sequences. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  by_contra h
  wlog h2 : s < t
  · rcases Ne.lt_or_lt h with (h3 | h3)
    · contradiction
    · apply this _ _ _ ht hs _ h3
      exact ne_comm.mp h
  set ε := t - s with hε
  have hε : 0 < ε := sub_pos.mpr h2
  obtain ⟨X, hX⟩ := hs (ε / 2) (by linarith)
  obtain ⟨Y, hY⟩ := ht (ε / 2) (by linarith)
  specialize hX (max X Y) (le_max_left X Y)
  specialize hY (max X Y) (le_max_right X Y)
  rw [abs_lt] at hX hY
  linarith

/-- The squeeze theorem (also known as the sandwich theorem). -/
theorem squeeze_theorem {x y z : ℕ → ℝ} {l : ℝ}
    (hx : TendsTo x l) (hy : TendsTo y l)
    (hle : ∀ n, x n ≤ z n ∧ z n ≤ y n) :
    TendsTo z l := by
  sorry

/-- A closed interval `[a, b]` in ℝ. -/
def closedInterval (a b : ℝ) : Set ℝ := {x | a ≤ x ∧ x ≤ b}

/-- Unfolding the definition of membership in a closed interval. -/
theorem closedInterval_def {a b : ℝ} {x : ℝ} : x ∈ closedInterval a b ↔ a ≤ x ∧ x ≤ b := by
  rfl

/-- Definition of a nested family of intervals:
    1) `a n ≤ b n` for all `n`.
    2) Each `[a(n+1), b(n+1)]` is contained in `[a n, b n]`. -/
def NestedIntervals (a b : ℕ → ℝ) : Prop :=
  (∀ n, a n ≤ b n)
  ∧ (∀ n, closedInterval (a (n+1)) (b (n+1)) ⊆ closedInterval (a n) (b n))

/-- The length of the interval `[a, b]` is `b - a`. -/
def intervalLength (a b : ℝ) : ℝ := b - a


lemma monotone_increasing_bounded_above_convergent
    (u : ℕ → ℝ)
    (hMono : ∀ n, u n ≤ u (n+1))          -- monotone increasing
    (hBound : ∃ M, ∀ n, u n ≤ M) :        -- bounded above
    ∃ L : ℝ, TendsTo u L := by
  sorry  -- Typical approach: use completeness to construct the limit.

lemma monotone_decreasing_bounded_below_convergent
    (u : ℕ → ℝ)
    (hMono : ∀ n, u (n+1) ≤ u n)          -- monotone decreasing
    (hBound : ∃ m, ∀ n, m ≤ u n) :        -- bounded below
    ∃ L : ℝ, TendsTo u L := by
  sorry

/-- If `a` is a monotone increasing sequence converging to `A`, then `a n ≤ A` for all `n`. -/
lemma monotone_increasing_seq_le_limit
    (a : ℕ → ℝ) (A : ℝ)
    (hMono : ∀ n, a n ≤ a (n+1))
    (hA : TendsTo a A) :
    ∀ n, a n ≤ A := by
  sorry

/--
  Nested Interval Theorem:
  Given sequences `(a n)`, `(b n)`, if they form a nested family of closed intervals
  and the length of these intervals `(b n - a n)` goes to `0`,
  then the intersection of all those intervals is exactly a single point.
 -/
theorem nestedIntervals_theorem
    {a b : ℕ → ℝ}
    (hNested : NestedIntervals a b)                      -- The condition of nested intervals
    (hLimit  : ∀ ε > 0, ∃ N, ∀ n ≥ N, (b n - a n) < ε) : -- Equivalent to (b n - a n) → 0
    ∃ c : ℝ, (⋂ n, closedInterval (a n) (b n)) = { c } := by

  /-
    Step 1: From `hNested`, we obtain the monotonicity of `a` and `b`, i.e.
    a(n+1) ≥ a(n) and b(n+1) ≤ b(n).
  -/
  have hMonotoneA : ∀ n, a n ≤ a (n+1) := by
    intro n
    let x := a (n+1)
    have hA_le_Bn1 : a (n+1) ≤ b (n+1) := hNested.1 (n+1)
    have hx1 : x ∈ closedInterval (a (n+1)) (b (n+1)) := by
      simp only [closedInterval, Set.mem_setOf_eq]
      exact ⟨le_rfl, hA_le_Bn1⟩
    have hx2 : x ∈ closedInterval (a n) (b n) := (hNested.2 n) hx1
    simp only [closedInterval, Set.mem_setOf_eq] at hx2
    exact hx2.1

  have hMonotoneB : ∀ n, b (n+1) ≤ b n := by
    intro n
    let y := b (n+1)
    have hA_le_Bn1 : a (n+1) ≤ b (n+1) := hNested.1 (n+1)
    have hy1 : y ∈ closedInterval (a (n+1)) (b (n+1)) := by
      simp only [closedInterval, Set.mem_setOf_eq]
      refine ⟨hA_le_Bn1, le_rfl⟩
    have hy2 : y ∈ closedInterval (a n) (b n) := (hNested.2 n) hy1
    simp only [closedInterval, Set.mem_setOf_eq] at hy2
    exact hy2.2

  /-
    Step 2: Show that `a` is bounded above and `b` is bounded below.
  -/
  have hBoundA : ∃ M, ∀ n, a n ≤ M := by
    use b 0
    intro n
    have ha_le_bn : a n ≤ b n := hNested.1 n
    apply le_trans ha_le_bn
    -- We want to show `b n ≤ b 0`, proven by monotonicity (decreasing) of b:
    induction n with
    | zero => rfl
    | succ k ih =>
      exact le_trans (hMonotoneB k) (ih (hNested.1 k))

  have hBoundB : ∃ m, ∀ n, m ≤ b n := by
    use a 0
    intro n
    -- Show `a 0 ≤ a n` (by monotonicity of `a`):
    have ha0_le_an : a 0 ≤ a n := by
      induction n with
      | zero => rfl
      | succ k ih => exact le_trans ih (hMonotoneA k)
      -- nice
    exact le_trans ha0_le_an (hNested.1 n)

  /-
    Step 3: By monotonicity and boundedness, both `a` and `b` converge.
  -/
  obtain ⟨A, hA⟩ := monotone_increasing_bounded_above_convergent a hMonotoneA hBoundA
  obtain ⟨B, hB⟩ := monotone_decreasing_bounded_below_convergent b hMonotoneB hBoundB

  /-
    Step 4: We know `(b n - a n) → 0`.
    Interpret that as `TendsTo (fun n => b n - a n) 0`.
  -/
  have subTendsToZero : TendsTo (fun n => b n - a n) 0 := by
    rw [TendsTo]
    intro ε hε
    obtain ⟨N, hN⟩ := hLimit ε hε
    use N
    intro n hn
    specialize hN n hn
    rwa [sub_zero, abs_of_nonneg]
    simpa using hNested.1 n

  /-
    Also, `(fun n => b n - a n)` should converge to `(B - A)`.
  -/
  have subTendsToBA : TendsTo (fun n => b n - a n) (B - A) := by
    sorry

  /-
    By the uniqueness of limits, `(B - A) = 0` and thus `A = B`.
  -/
  have equality : A = B := by
    have h := tendsTo_unique (fun n => b n - a n) 0 (B - A) subTendsToZero subTendsToBA
    linarith

  let c := A

  /-
    Step 5: We show the intersection of all `[a n, b n]` is the single point `{c}`.
  -/
  have hc_unique : ∀ c', (c' ∈ ⋂ n, closedInterval (a n) (b n)) → c' = c := by
    intro c' hc'
    -- From `c' ∈ ⋂ n, [a n, b n]`, we get `∀ n, a n ≤ c' ≤ b n`.
    have he : ∀ n, a n ≤ c' ∧ c' ≤ b n := by
      rw [Set.mem_iInter] at hc'
      intro n
      let h_mem := hc' n
      rw [closedInterval, Set.mem_setOf_eq] at h_mem
      exact h_mem
    -- Define x(n) = c' as a constant sequence, which trivially converges to c'.
    let x : ℕ → ℝ := fun _ => c'
    have hx_c' : TendsTo x c' := by
      intro ε hε
      use 0
      intro n _
      simp
      linarith
    -- By the squeeze theorem: a(n) → c and b(n) → c, and a(n) ≤ x(n) ≤ b(n), hence x(n) → c.
    have hx_c : TendsTo x c := by
      -- We know hA: TendsTo a c, hB: TendsTo b c, and a(n) ≤ c' ≤ b(n).
      have hC : TendsTo b A := by rwa [equality]
      apply squeeze_theorem hA hC
      intro n
      exact ⟨(he n).1, (he n).2⟩
    -- By the uniqueness of limits, c' = c.
    exact tendsTo_unique x c' c hx_c' hx_c

   -- Finally, we conclude that the intersection is exactly `{c}`.
  use c
  apply Set.ext
  intro x
  constructor
  . intro hx
    exact hc_unique x hx
  . intro hx
    subst hx
    rw [Set.mem_iInter]
    intro n
    rw [closedInterval, Set.mem_setOf_eq]
    -- Since a ≤ A and A ≤ b by monotonicity in the limit, c = A is always in [a n, b n].
    -- We can also apply a standard argument that the limit of a(n) ≤ A, and similarly B = A ≤ b(n).
    sorry
