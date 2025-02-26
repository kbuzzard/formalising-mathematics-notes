import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Order.Bounds.Basic
open Set
/-
首先，定义序列为自然数到实数的函数。
-/
-- English please!

def Sequence := ℕ → ℝ

instance : Neg Sequence where
  neg s := λ n => - s n  -- 逐元素取反

def Sequence.abs (a : Sequence) : Sequence := λ n => |a n|

@[simp] theorem seq_abs_eq (a : Sequence) (n : ℕ) : a.abs n = |a n| := by rfl

/-- Proposition that a sequence is bounded above, i.e. all terms lie within `(-∞, M]`. -/
def Sequence.bounded_above (a : Sequence) : Prop := ∃ M, ∀ n, a n ≤ M

/-- Proposition that a sequence is bounded above, i.e. all terms lie within `[m, ∞)`. -/
def Sequence.bounded_below (a : Sequence) : Prop := ∃ m, ∀ n, m ≤ a n

/-- Proposition that a sequence is bounded above and below, i.e. all terms lie within `[-M, M]`. -/
def Sequence.bounded (a : Sequence) : Prop := a.abs.bounded_above

/-- Proof that a sequence is bounded in absolute value
if and only if it is bounded both above and below. -/
theorem bounded_iff_above_below {a : Sequence} : a.bounded ↔ a.bounded_above ∧ a.bounded_below := by
  constructor
  -- Make sure to use · when you have multiple goals.
  -- 证明必要性：绝对值有界蕴含上下界有界
  · intro hb
  -- 分解绝对值有界的假设，得到界M和对应的性质hM
    cases' hb with M hM
    constructor
    -- 构造上界的存在性证明
    · use M
      intro n
      -- 应用le_of_abs_le定理，由|s n| ≤ M推导s n ≤ M
      exact le_of_abs_le (hM n)
    -- 构造下界的存在性证明
    · use -M
      intro n
      -- 应用neg_le_of_abs_le定理，由|s n| ≤ M推导-M ≤ s n
      exact neg_le_of_abs_le (hM n)
      -- 证明充分性：上下界有界蕴含绝对值有界
  · rintro ⟨ha, hb⟩
    -- 分解上下界有界的假设，得到上界M和下界m，及其对应的性质hM和hm
    cases' ha with M hM
    cases' hb with m hm
    -- 使用max M (-m)作为共同的界
    use max M (-m)
    intro n
    -- 分情况讨论s n的正负性
    by_cases h : a n ≤ 0
    · -- 情况1：s n ≤ 0
      rw [seq_abs_eq, abs_of_nonpos h]
      -- 应用le_max_of_le_right定理，由-M ≤ s n推导|s n| ≤ max M (-m)
      exact le_max_of_le_right (neg_le_neg (hm n))
    · -- 情况2：s n > 0
      push_neg at h
      rw [seq_abs_eq,  abs_of_pos h]
      -- 应用le_max_of_le_left定理，由s n ≤ M推导|s n| ≤ max M (-m)
      exact le_max_of_le_left (hM n)


/-
定义序列收敛到某个极限L。
-/
def ConvergesTo (a : Sequence) (L : ℝ) :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

/-
定义柯西序列。
-/
def CauchySequence (a : Sequence) :=
  ∀ ε > 0, ∃ N > 0,  ∀ m ≥ N, ∀ n ≥ N, |a m - a n| < ε

/-- A real number belongs to the finite prefix set if and only if it is the value taken by
      the sequence `s` for some term before the `n`-th term. -/

noncomputable def sequence_set (a : Sequence) (n : ℕ) : Finset ℝ :=
  (Multiset.map a (Multiset.range n)).toFinset
  -- This would also have worked: `(Finset.range n).image a`

@[simp] theorem mem_sequence_set {a : Sequence} {n : ℕ} {x : ℝ} :
  x ∈ sequence_set a n ↔ ∃ k, k < n ∧ a k = x := by
  simp only [sequence_set, Multiset.mem_toFinset, Multiset.mem_map, Multiset.mem_range]

theorem sequence_set_nonempty (a : Sequence) {n : ℕ} (hn : n > 0) : (sequence_set a n).Nonempty :=
  ⟨a 0, mem_sequence_set.mpr ⟨0, hn, rfl⟩⟩

theorem sequence_set_max (a : Sequence) {n : ℕ} (hn : n > 0) :
    ∃ m, m < n ∧ ∀ k < n, a k ≤ a m := by
  let fs := sequence_set a n
  obtain ⟨m, hm⟩ := mem_sequence_set.mp (fs.max'_mem (sequence_set_nonempty a hn))
  use m
  constructor
  · exact hm.1
  intro k hk
  rw [hm.2]
  exact fs.le_max' (a k) (mem_sequence_set.mpr ⟨k, hk, rfl⟩)

theorem sequence_set_min (a : Sequence) {n : ℕ} (hn : n > 0) :
    ∃ m, m < n ∧ ∀ k < n, a m ≤ a k := by
  rcases sequence_set_max (-a) hn with ⟨M, Mpos, hM⟩
  use M
  constructor
  · exact Mpos
  · intro k hk
    specialize hM k hk
    exact neg_le_neg_iff.mp hM

theorem sequence_set_bounded (a: Sequence) {n: ℕ} (hn : n > 0) :
    ∃ M, ∀ k < n, |a k| ≤ M := by
  rcases sequence_set_max a hn with ⟨M₀, Mpos₀, hM₀⟩
  rcases sequence_set_min a hn with ⟨M₁, Mpos₁, hM₁⟩
  use max (a M₀) (- a M₁)
  intro k hk
  specialize hM₀ k hk
  specialize hM₁ k hk
  cases' le_total 0 (a k) with h h <;>
  simp_all [abs_of_nonneg, abs_of_nonpos, le_refl]


lemma cauchy_bounded {a : Sequence}: CauchySequence a → a.bounded := by
  -- 使用柯西序列定义，取ε=1，存在N使得当m, n ≥ N时，|a m - a n| < 1
  intro Sa
  specialize Sa 1 (by norm_num)
  rcases Sa with ⟨N, Npos, hN⟩
  specialize hN N (by linarith)
  -- 已知条件：当 m, n ≥ N 时，|a m - a n| < 1
  have h1 : ∀ n ≥ N, |a n| < 1 + |a N| := by
    intro n npos
    specialize hN n npos
    -- 使用绝对值不等式定理abs_sub_lt_iff将条件转化为两个不等式
    rw [abs_sub_lt_iff] at hN
  -- 分解h为h₁和h₂
    cases' hN with h₁ h₂
  -- 对两种情况分别应用绝对值不等式定理abs_lt，并使用线性算术解决
    cases' le_total 0 (a n) with hn' hn' <;>
      cases' le_total 0 (a N) with hN hN <;>
        simp_all [abs_of_nonneg, abs_of_nonpos, sub_nonneg, sub_nonpos] <;>
        linarith
  have h2 : ∃ M, ∀ k < N, |a k| ≤ M := by exact sequence_set_bounded a Npos
  rcases h2 with ⟨M, hM⟩
  use max M (1 + |a N|)
  intro n
  -- 对于任意自然数n，我们考虑其与N的关系
  cases' le_or_lt N n with h₀ h₀
  · specialize h1 n h₀
    simp_all only [gt_iff_lt, ge_iff_le, seq_abs_eq, le_sup_iff]
    right
    linarith
  · specialize hM n h₀
    simp_all [abs_of_nonneg, abs_of_nonpos, sub_nonneg, sub_nonpos]

/-
证明柯西序列收敛。
-/

noncomputable def b_n {a : Sequence} (h : CauchySequence a) : ℕ → ℝ := fun n =>
  -- 获取柯西序列的有界性证明
  have h1: a.bounded := cauchy_bounded h
  -- 确保集合 {a_i | i ≥ n} 非空且有上界
  have h_nonempty : Set.Nonempty (Set.range (fun i : ℕ => a (n + i))) :=
    ⟨a n, ⟨0, by simp⟩⟩
  have h_bdd_above : BddAbove (Set.range (fun i : ℕ => a (n + i))) := by
    rcases h1 with ⟨B, hB⟩
    use B
    intro x rx
    rcases Set.mem_range.1 rx with ⟨i, hi⟩
    rw [← hi]
    specialize hB (n + i)
    rw [Sequence.abs] at hB
    exact le_of_abs_le hB
  -- 使用 sSup 定义上确界
  sSup (Set.range (fun i : ℕ => a (n + i)))

lemma b_n_ge_a_i {a : Sequence} (h : CauchySequence a) : ∀ n i, i ≥ n → b_n h n ≥ a i := by
  intro n i hi
  have h1 : a.bounded := cauchy_bounded h
  /- Since `b_n` is defined as the supremum of the set `{a_i | i ≥ n}`,
   we need to show that `a_i` is in this set.-/
  have h1 : a i ∈ Set.range (fun i : ℕ => a (n + i)) := by
    -- `i ≥ n` implies `i = n + (i - n)` for some `i - n ≥ 0`.
    use i - n
    -- Simplify the expression to show that `a_i` is indeed in the set.
    simp [Nat.add_sub_of_le hi]
  -- By the definition of supremum, `b_n` is an upper bound for the set `{a_i | i ≥ n}`.
  -- Therefore, `b_n` is greater than or equal to any element in this set, including `a_i`.
  have h_bdd_above : BddAbove (Set.range (fun i : ℕ => a (n + i))) := by
    have h2 : a.bounded := cauchy_bounded h
    rcases h2 with ⟨B, hB⟩
    use B
    intro x rx
    rcases Set.mem_range.1 rx with ⟨i, hi⟩
    rw [← hi]
    specialize hB (n + i)
    rw [Sequence.abs] at hB
    exact le_of_abs_le hB
  exact le_csSup h_bdd_above h1

theorem cauchy_converges {a : Sequence} (h : CauchySequence a) : ∃ L : ℝ, ConvergesTo a L := by
  -- 使用实数的完备性，这里简化为存在极限。
  have h1 : a.bounded := cauchy_bounded h
  let b := b_n h
  -- 定义 `b_n = sup {a_i | i ≥ n}`
  have h_monotone : ∀ m n, m ≤ n → b m ≥ b n := by
    intro m n hmn
    -- 利用上确界的性质进行证明
    have h2 : ∀n i, i ≥ n → b n ≥ a i := by exact b_n_ge_a_i h
    have h3 : ∀n i, i ≥ (n+1) → b n ≥ a i := by
      intro n i hni
      apply h2
      linarith
    have h4 :  ∀ n, sSup {a i | i ≥ n + 1} = b (n + 1) := by
      intro n
  -- 步骤1：证明集合 {a i | i ≥ n + 1} 与 Set.range (fun i : ℕ => a (n + 1 + i)) 等价
      have h_set_eq : {a i | i ≥ n + 1} = Set.range (fun i : ℕ => a (n + 1 + i)) := by
        ext x  -- 应用集合扩展性公理，证明元素相同
        constructor <;> simp_all [Set.mem_setOf_eq, Set.mem_range]
        · -- 子目标1：{a i | i ≥ n + 1} ⊆ Set.range (fun i => a (n + 1 + i))
          intro i hi rfl  -- 解构存在量词，得到i ≥ n + 1且x = a i
          use i - (n + 1)      -- 构造k = i - (n + 1)，使得i = n + 1 + k
          have h₁ : n + 1 + (i - (n + 1)) = i := by exact Nat.add_sub_of_le hi
          rw [h₁]
          exact rfl            -- 验证k ≥ 0且i = n + 1 + k
        · -- 子目标2：Set.range (fun i => a (n + 1 + i)) ⊆ {a i | i ≥ n + 1}
          intro k rfl      -- 解构存在量词，得到x = a (n + 1 + k)
          use n + 1 + k        -- 构造i = n + 1 + k
          constructor
          · apply Nat.le_add_right
          · exact rfl            -- 验证i ≥ n + 1且x = a i
  -- 步骤2：由于集合等价，它们的上确界相等
      rw [h_set_eq]  -- 将原集合替换为等价的Set.range形式
  -- 步骤3：根据b的定义，直接得出等式成立
      rfl  -- b (n + 1) 定义为sSup (Set.range (fun i => a (n + 1 + i)))，与右侧完全匹配
  -- 选择i = N + n + 1，确保i ≥ n + 1

    have h5 :∀ n : ℕ, b n ≥ sSup {a i | i ≥ n + 1} := by
      intro n'
      have h_nonempty : Set.Nonempty {a i | i ≥ n' + 1} := by
        use a (n' + 1)
        exact ⟨n' + 1, by simp⟩
      have h_le : ∀ x ∈ {a i | i ≥ n' + 1}, x ≤ b n' := by
        intro x hx
        rcases hx with ⟨k, hk, rfl⟩
        specialize h3 n' k hk -- 使用 n' 而不是 n
        linarith
      exact csSup_le h_nonempty h_le
    have h6 : ∀ n : ℕ, b n ≥ b (n + 1) := by
      intro n'
      specialize h5 n'
      rw [h4 n'] at h5
      exact h5
    have ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmn  -- 分解得到k和等式hk : n = m + k
    rw [hk] at hmn ⊢
  -- 对k进行归纳
    clear hk
    induction' k with k ih
  -- 基例：k = 0时，n = m + 0 = m，显然成立
    case zero => simp
  -- 归纳步骤：假设对于k，b(m) ≥ b(m + k)，需要证明对于k + 1，b(m) ≥ b(m + (k + 1))
    case succ =>
    -- 根据已知条件，b(m + k) ≥ b(m + k + 1)
    -- 结合归纳假设和已知条件，得到b(m) ≥ b(m + k + 1)
    specialize h6 (m + k)
    calc
      b m ≥ b (m + k) := ih (Nat.le_add_right m k)
      _ ≥ b (m + k + 1) := h6
  let L := sInf {b n| n:ℕ}
  use L
  intro ε hε
  have hε₁ : 0 < ε/2 := by
    linarith
  specialize h (ε/2) hε₁
  rcases h with ⟨N, hN, h'⟩
  have h'' : ∀ m ≥ N, ∀ n ≥ N, a n - ε / 2 < a m ∧ a m < a n + ε / 2 := by
    intro m hm n hn
    specialize h' m hm n hn
    rw [abs_sub_lt_iff] at h'
    cases' h' with h_left h_right
    constructor
    · linarith
    · linarith
  have Ineq_1 : ∀ m ≥ N, ∀ n ≥ N, a n - ε / 2 < b N ∧ b N < a n + ε / 2 := by
    intro m hm n hn
    specialize h'' m hm n hn
    cases' h'' with h_left h_right
    constructor
    · have hsSup : a n - ε / 2 < sSup {a m | m ≥ N} := by
        have h2 : a m ≤ sSup {a m | m ≥ N} := by
          have h_mem : a m ∈ {x | ∃ m ≥ N, a m = x} := ⟨m, hm, rfl⟩
          have h_bdd_above : BddAbove (setOf {a m | m ≥ N}) := by
            rcases h1 with ⟨B, hB⟩
            use B
            intro x rx
            rcases Set.mem_setOf_eq.1 rx with ⟨i, hi⟩
            rw [← hi]
            specialize hB (n + i)
            rw [Sequence.abs] at hB
            exact le_of_abs_le hB
          exact le_csSup h_bdd_above h_mem
        linarith
      have h_eq_sup : sSup {a m | m ≥ N} = b N := by
    -- 根据 b N 的定义
        rw [b_n]
    -- 证明集合相等
        ext x
        constructor
    -- 子目标1：{a m | m ≥ N} ⊆ {a i | i ≥ N}
        · intro hx
          rcases hx with ⟨m, hm, rfl⟩
          use m
          exact hm
    -- 子目标2：{a i | i ≥ N} ⊆ {a m | m ≥ N}
        · intro hx
          rcases hx with ⟨i, hi, rfl⟩
          use i
          exact hi
      linarith
    · sorry
  have Ineq_2 : ∀ n ≥ N, a n - ε / 2 ≤ L ∧ L ≤ a n + ε / 2 := by
    sorry
  have Ineq_3 : ∀ n ≥ N, |L - a n| ≤ ε / 2 ∧ ε / 2 < ε := by
    intro N' hN'
    specialize Ineq_2 N' hN'
    cases' Ineq_2 with h1 h2
    constructor <;>
    cases' le_total 0 (L - a N') with h h <;>
    simp_all [abs_of_nonneg, abs_of_nonpos, sub_nonneg, sub_nonpos]
  -- 对于 L - a_N' ≥ 0 的情况，使用 h2 进行推导
    <;> linarith

  use N
  intro n hn
  specialize Ineq_3 n hn
  cases' Ineq_3 with h1 h2
  rw [abs_sub_comm] at h1
  have h3 : |a n - L| < ε := by exact lt_of_le_of_lt h1 h2
  exact h3
