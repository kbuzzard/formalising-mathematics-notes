import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import Mathlib.Topology.Instances.Real

open Set

/-
cid:02209247

Proof of the Intermediate Value Theorem (IVT) using Lean4.

The IVT states that if a function \( f \) is continuous on \([a, b]\) and
\( c \) is between \( f(a) \) and \( f(b) \), then there exists some \( x \)
in \([a, b]\) such that \( f(x) = c \).

**Proof Outline:**
1. **Case 1:** \( f(a) < c < f(b) \)
   - Construct the set \( S_c = \{ y \in [a, b] \mid f(y) < c \} \).
   - Show \( S_c \) is non-empty and bounded above, hence has a least upper bound \( x \).
   - Prove \( f(x) = c \) by contradiction using continuity and the properties of supremum.

2. **Case 2:** \( f(b) < c < f(a) \)
   - Define \( g(x) = -f(x) \), which is continuous on \([a, b]\).
   - Apply Case 1 to \( g \) and \( -c \), obtaining \( x \) such that \( g(x) = -c \).
   - Conclude \( f(x) = c \).

**Main Theorem:**
- Handle trivial cases where \( c = f(a) \) or \( c = f(b) \).
- For non-trivial cases, use the lemma `exists_eq_c_of_continuous_on_interval`
for both scenarios.
-/

-- Define continuity at a point using the epsilon-delta definition
def continuous_at (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε

-- Define continuity on an interval by requiring continuity at every point within the interval
def continuous_on (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Icc a b, continuous_at f x

-- Lemma handling the case where f(a) < c < f(b)
lemma exists_eq_c_of_continuous_on_interval (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : continuous_on f a b) (c : ℝ)
    (hfa_c_fb : f a < c ∧ c < f b) : ∃ x ∈ Set.Icc a b, f x = c := by

  -- Define the set S_c as all y in [a, b] where f(y) < c
  let S_c : Set ℝ := {y | a ≤ y ∧ y ≤ b ∧ f y < c}
  -- Show that a is in S_c, establishing S_c is non-empty
  have h_a_in_S_c : a ∈ S_c := by
    simp only [mem_setOf_eq, le_refl, true_and, S_c]
    -- this was a nonterminal simp, don't have those!
    constructor
    · exact hab  -- a ≤ a (trivially true)
    · exact hfa_c_fb.1  -- f(a) < c
    -- you could also have fixed this with
    -- simp [S_c, *]
  have h_S_c_nonempty : S_c.Nonempty := by
    use a  -- Since a ∈ S_c, S_c is non-empty
  -- Establish that S_c is bounded above by b
  have h_S_c_bdd_above : BddAbove S_c := by
    use b  -- All elements in S_c are ≤ b
    intro y hy
    exact hy.2.1  -- y ≤ b from the definition of S_c
  -- Obtain the least upper bound (supremum) of S_c using completeness of real numbers
  obtain ⟨x, hx⟩ : ∃ x, IsLUB S_c x :=
    Real.exists_isLUB h_S_c_nonempty h_S_c_bdd_above
  -- Show x is within [a, b]
  have hx_mem : x ∈ Icc a b := by
    constructor
    · exact hx.1 h_a_in_S_c  -- a ≤ x (since x is an upper bound and a ∈ S_c)
    · exact hx.2 (fun y hy ↦ hy.2.1)  -- x ≤ b (since all y ∈ S_c are ≤ b)
  -- Prove f(x) = c by contradiction using continuity and supremum properties
  have h_fx_eq_c : f x = c := by
    apply le_antisymm
    -- Assume f(x) > c and derive a contradiction
    · by_contra h_fx_gt_c
      -- Define ε = f(x) - c > 0
      let ε : ℝ := f x - c
      have h_cont := hf x hx_mem  -- Continuity of f at x
      have h_c_lt_fx : c < f x := lt_of_not_le h_fx_gt_c
      have h_ε_pos : 0 < ε := sub_pos.mpr h_c_lt_fx
      -- Obtain δ > 0 such that |f(y) - f(x)| < ε when |y - x| < δ
      obtain ⟨δ, hδ_pos, hδ⟩ := h_cont (f x - c) h_ε_pos
      -- Construct a point m such that m < x and m is an upper bound of S_c,
      -- contradicting the assumption that x is the supremum of S_c
      -- Show m ∈ (x - δ, x + δ) ∩ [a, b]
      have h_m_exists : max a (x - δ / 2) ∈ Icc a b ∧
      max a (x - δ / 2) - x < δ ∧ x - max a (x - δ / 2) < δ := by
        constructor
        · constructor
          · apply le_max_left  -- a ≤ max a (x - δ/2)
          · rcases hx_mem with ⟨hx_left, hx_right⟩
            cases' le_total a (x - δ / 2) with h h <;>
              simp_all [max_eq_left, max_eq_right, sub_le_iff_le_add]
            linarith  -- Verify max a (x - δ/2) ≤ b
        · constructor
          · rcases hx_mem with ⟨hx_left, hx_right⟩
            cases' le_total a (x - δ / 2) with h h <;>
              simp_all [sup_eq_left.mpr h, sup_eq_right.mpr h, sub_nonneg, sub_nonpos] <;>
            linarith  -- Verify |max a (x - δ/2) - x| < δ
          · rcases hx_mem with ⟨hx_left, hx_right⟩
            cases' le_total a (x - δ / 2) with h h <;>
              simp_all [max_eq_left, max_eq_right, sub_lt_iff_lt_add]
            linarith  -- Verify |x - max a (x - δ/2)| < δ
      -- Show max a (x - δ / 2) < x
      have h_max_lt_x : max a (x - δ / 2) < x := by
        have hδ_half_pos : 0 < δ / 2 := by linarith
        have h_sub_lt : x - δ / 2 < x := by linarith
        cases' le_total a (x - δ / 2) with h h <;>
        simp_all
        have h_a_lt_x : a < x := by
          by_contra h_a_ge_x
          have h_a_eq_x : a = x := by linarith [hx_mem.1, hx_mem.2]
          subst h_a_eq_x
          linarith [hfa_c_fb.1, h_c_lt_fx]
        exact h_a_lt_x
      -- Show f(max a (x - δ / 2)) > f(x) - ε
      have h_f_max_gt_fx_sub_ε : f (max a (x - δ / 2)) > f x - ε := by
        have h_m_in_ball : |max a (x - δ / 2) - x| < δ := by
          have h_lt_x : max a (x - δ / 2) < x := h_max_lt_x
          cases le_total (max a (x - δ / 2)) x with
          | inl h_le =>
            rw [abs_of_nonpos (sub_nonpos.mpr h_le)]
            linarith [hδ_pos]
          | inr h_le =>
            linarith [h_lt_x]
        have h_fm_fx_lt_ε : |f (max a (x - δ / 2)) - f x| < ε := hδ _ h_m_in_ball
        linarith [abs_sub_lt_iff.mp h_fm_fx_lt_ε]
      -- Show that no y in (max a (x - δ/2), x) can be in S_c
      have h_y_not_in_S_c : ∀ y, max a (x - δ / 2) < y ∧ y < x → y ∉ S_c := by
        intro y hy
        simp only [S_c, Set.mem_setOf_eq, not_and, not_lt] at *
        intro h_y_in_interval
        have h_y_lt_x : y < x := hy.2
        have h_y_ge_max : max a (x - δ / 2) < y := hy.1
        have h_fy_fx_lt_ε : |f y - f x| < ε := hδ y (by
          rw [abs_lt]
          constructor
          · linarith [h_y_lt_x]
          · have h_sub : x - y < δ := by linarith [h_y_ge_max, hx_mem.1, hx_mem.2]
            linarith)
        have h_fy_gt_c : f y > c := by
          rw [abs_lt] at h_fy_fx_lt_ε
          have h_ε_def : ε = f x - c := rfl
          linarith [h_ε_def, hfa_c_fb.1, h_c_lt_fx, h_fy_fx_lt_ε.1, h_fy_fx_lt_ε.2]
        exact fun _ => h_fy_gt_c.le
      -- Show max a (x - δ/2) is an upper bound for S_c
      have h_max_upper_bound : ∀ y ∈ S_c, y ≤ max a (x - δ / 2) := by
        intro y hy
        by_contra h_y_gt_max
        have h_y_in_interval : max a (x - δ / 2) < y ∧ y < x := by
          constructor
          · linarith [h_y_gt_max]
          · apply lt_of_le_of_ne (hx.1 hy)
            intro h_y_eq_x
            have h_x_in_S_c : x ∈ S_c := by simpa [h_y_eq_x] using hy
            have h_fx_lt_c : f x < c := h_x_in_S_c.2.2
            linarith [h_c_lt_fx]
        exact h_y_not_in_S_c y h_y_in_interval hy
      -- Contradiction: x ≤ max a (x - δ/2) but max a (x - δ/2) < x
      have h_x_le_max : x ≤ max a (x - δ / 2) := by
        exact hx.2 (fun y hy => h_max_upper_bound y hy)
      linarith [h_x_le_max, h_max_lt_x]
    -- Assume f(x) < c and derive a contradiction
    · by_contra h_fx_lt_c
      -- Define ε = c - f(x) > 0
      let ε : ℝ := c - f x
      have h_cont := hf x hx_mem  -- Continuity of f at x
      have h_fx_lt_c : f x < c := lt_of_not_le h_fx_lt_c
      have h_ε_pos : 0 < ε := sub_pos.mpr h_fx_lt_c
      -- Obtain δ > 0 such that |f(y) - f(x)| < ε when |y - x| < δ
      obtain ⟨δ, hδ_pos, hδ⟩ := h_cont (c - f x) h_ε_pos
      -- Show x < b
      have h_x_lt_b : x < b := by
        apply lt_of_le_of_ne (hx_mem.2)
        intro h_eq
        subst h_eq
        exact hfa_c_fb.2.ne (by linarith [hx_mem.2])
      -- Construct a point y where f(y) < c but y > x, contradicting x being the supremum
      let y := x + (1/2) * min δ (b - x)
      -- Show y ∈ S_c
      have h_y_in_S_c : y ∈ S_c := by
        simp [S_c] -- another nonterminal simp
        constructor
        · -- Verify a ≤ y
          have h_a_le_x : a ≤ x := hx_mem.1
          have h_min_nonneg : 0 ≤ min δ (b - x) := by
            apply le_min
            · linarith [hδ_pos]  -- δ ≥ 0
            · linarith [h_x_lt_b]  -- b - x > 0
          refine le_trans h_a_le_x (le_add_of_nonneg_right ?_)
          positivity
        · constructor
          · -- Verify y ≤ b
            have h_min_le : min δ (b - x) ≤ b - x := by
              apply min_le_right
            calc
              y = x + 1 / 2 * (min δ (b - x)) := rfl
              _ ≤ x + 1 / 2 * (b - x) := by gcongr
              _ = x + (b - x) / 2 := by ring
              _ = (x + b) / 2 := by ring
              _ ≤ b := by linarith [h_x_lt_b] -- nice!
          · -- Verify f(y) < c
            have h_y_near_x : |y - x| < δ := by
              unfold y
              rw [abs_of_nonneg]
              all_goals
                cases' le_total δ (b - x) with h h <;>
                simp_all [min_eq_left, min_eq_right, sub_pos, mul_comm]
              <;> linarith [hδ_pos, h_x_lt_b]
            have h_fy_bound : |f y - f x| < c - f x := by
              apply hδ y h_y_near_x
            have h_fy_lt_c : f y < c := by
              rw [abs_lt] at h_fy_bound
              linarith [h_fy_bound.2]
            exact h_fy_lt_c
      -- Show y > x
      have h_y_gt_x : x < y := by
        unfold y
        have h_min_pos : 0 < δ ⊓ (b - x) := by
          apply lt_min
          · exact hδ_pos
          · linarith [h_x_lt_b]
        have h_half_min_pos : 0 < (1 / 2 : ℝ) * (δ ⊓ (b - x)) := by
          apply mul_pos
          · norm_num
          · exact h_min_pos
        linarith
      -- Contradiction: y > x and y ∈ S_c, but x is the supremum
      have h_y_not_in_S_c : y ∉ S_c := by
        intro h_y_in_S_c
        linarith [hx.1 h_y_in_S_c]
      exact h_y_not_in_S_c h_y_in_S_c
  -- Conclude the existence of x in [a, b] with f(x) = c
  exact ⟨x, hx_mem, h_fx_eq_c⟩

-- Main theorem: Intermediate Value Theorem
theorem intermediate_value_theorem (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : continuous_on f a b) :
    ∀ c ∈ Set.Icc (min (f a) (f b)) (max (f a) (f b)), ∃ x ∈ Set.Icc a b, f x = c := by
  intro c hc
  -- Handle trivial cases where c equals f(a) or f(b)
  by_cases h : f a = c ∨ f b = c
  · cases h with
    | inl hfa_eq_c =>
      -- If c equals f(a), then x = a satisfies the theorem
      have ha_mem : a ∈ Icc a b := ⟨le_refl a, hab⟩
      exact ⟨a, ha_mem, hfa_eq_c⟩
    | inr hfb_eq_c =>
      -- If c equals f(b), then x = b satisfies the theorem
      have hb_mem : b ∈ Icc a b := by
        refine ⟨hab, le_refl b⟩
      exact ⟨b, hb_mem, hfb_eq_c⟩
  · -- Handle non-trivial cases where c is strictly between f(a) and f(b)
    have h_new : (f a < c ∧ c < f b) ∨ (f b < c ∧ c < f a) := by
      -- Decompose the assumption h : ¬(f a = c ∨ f b = c) into f a ≠ c and f b ≠ c
      have h₁ : f a ≠ c := by
        intro h_eq; apply h; left; exact h_eq
      have h₂ : f b ≠ c := by
        intro h_eq; apply h; right; exact h_eq
      cases' le_total (f a) (f b) with h₀ h₀
      · left
        constructor
        · exact lt_of_le_of_ne (by simp_all
          [ge_iff_le, le_inf_iff, le_sup_iff, h₀, true_and, and_true]) h₁
        · exact lt_of_le_of_ne (by simp_all
          [ge_iff_le, le_inf_iff, le_sup_iff, h₀, true_and, and_true]) h₂.symm
      · right
        constructor
        · exact lt_of_le_of_ne (by simp_all
          [ge_iff_le, le_inf_iff, le_sup_iff, h₀, true_and, and_true]) h₂
        · exact lt_of_le_of_ne (by simp_all
          [ge_iff_le, le_inf_iff, le_sup_iff, h₀, true_and, and_true]) h₁.symm
    cases h_new with
    | inl hfa_c_fb =>
      -- Apply the lemma for the case f(a) < c < f(b)
      exact exists_eq_c_of_continuous_on_interval f a b hab hf c hfa_c_fb
    | inr hfb_c_fa =>
      let g : ℝ → ℝ := fun x => -f x
      have hg_cont : continuous_on g a b := by
        intro x hx
        simp only [continuous_at, g]
        intro ε εpos
        obtain ⟨δ, δpos, hδ⟩ := hf x hx ε εpos
        use δ, δpos
        intro y hy
        simp only [g, neg_sub_neg] at hδ hy ⊢
        rw [abs_lt] at *
        cases' abs_lt.mp (hδ y (abs_lt.mpr hy)) with h₁ h₂
        constructor <;> linarith [h₁, h₂]
      have h_neg_c_in_interval : g a < -c ∧ -c < g b := by
        constructor
        . simp [g]
          linarith [hfb_c_fa.2]
        . simp [g]
          linarith [hfb_c_fa.1]
      -- Apply the existence theorem to g and -c
      obtain ⟨x, hx_mem, hx_eq⟩ := exists_eq_c_of_continuous_on_interval
        g a b hab hg_cont (-c) h_neg_c_in_interval
      use x, hx_mem
      simp [g] at hx_eq
      linarith
