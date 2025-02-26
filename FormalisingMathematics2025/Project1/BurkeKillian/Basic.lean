import Mathlib.Tactic
import Mathlib.Init

/-! In this document we define what it means for a real-valued function to be differentiable,
and prove that at a local maximum, if the derivative of a function exists, it must vanish.
Submitted as the first coursework for 'Formalising Mathematics 2025' by Killian Burke -/

/-! Definitions -/

/-- For 'f' a real-valued function, encodes 'lim_x→a f(x) = b' -/
def LimFun_to (f : ℝ → ℝ) (a : ℝ) (b : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, x ≠ a → |x - a| < δ → |f x - b| < ε
/-- 'f' is differentiable at 'a' with derivative 'b' when evaluated at 'a' -/
def MyDifferentiableAt (f : ℝ → ℝ) (a : ℝ) (b : ℝ ) : Prop :=
  LimFun_to (fun h => (f (a + h) - f a) / h) 0 b
/-- 'a' is a local maximum of 'f' -/
def CritPoint_max (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ ε > 0, ∀ x : ℝ, |x - a| < ε → f a - f x > 0

/-! The Theorem -/

/-- If 'f' is differentiable at its local maximum 'a',
then the derivative evaluated at 'a' must be '0' -/
theorem Max_is_stationary (f : ℝ → ℝ) (a : ℝ)
  (a_max : CritPoint_max f a) (b_diff : ∃ b : ℝ, MyDifferentiableAt f a b) :
  -- BM comments:
  -- p ∧ q → r is equivalent to p → q → r, and then might as well put stuff before
  -- the colon
    MyDifferentiableAt f a 0 := by
--Unfolding definitions:
  rcases b_diff with ⟨b, diff⟩
  unfold MyDifferentiableAt LimFun_to at diff --Not necessary, but helps with readability
  unfold CritPoint_max at a_max
  rcases a_max with ⟨δ1, δ1_pos, max⟩
--Split into 3 cases: b>0, b<0, or b=0
  cases eq_or_ne b 0 with -- BM: there's also `rcases eq_or_ne b 0 with rfl | hb`
  | inl b_zero => -- Obviously true if b is 0; this could have been done at the VERY start
      rw [b_zero] at diff
      exact diff

  | inr b_nonzero => --When b ≠ 0
    specialize diff (|b| / 2) --This ε will lead to a contradiction later on

    have b_half : 0 < |b| / 2 := by simpa
    --Peel off the quantifiers:
    specialize diff b_half
    rcases diff with ⟨δ2, δ2_pos, diff⟩
    let δ := min δ1 δ2 --Taking the minimum allows the use of diff and max at the same time

    have δ_pos : δ > 0 := lt_min δ1_pos δ2_pos

    intro ε1 ε1_pos
    use δ, δ_pos
    rintro x x_nonzero x_lt_δ
    /- ^Really we shouldn't need to touch the goal at all, but I want to grab the 'x'
    inside because it already has all the properties I need without defining them again -/
    simp only [sub_zero] at x_lt_δ

    have x_properties : x ≠ 0 ∧ |x| < δ2 := ⟨x_nonzero, x_lt_δ.trans_le (min_le_right _ _)⟩

    have x_lt_δ1 : |x| < δ1 := x_lt_δ.trans_le (min_le_left _ _)

    --we will contradict this
    have good : |b| / 2 < |b| := div_two_lt_of_pos (by simpa)

    cases lt_or_gt_of_ne b_nonzero with  --Check b<0 and b>0
    | inl b_neg =>
      specialize diff (-|x|) --Contradiction for negative x
      dsimp only at diff
      rw [ne_eq, neg_eq_zero, abs_eq_zero, sub_zero, abs_neg, abs_abs, ← sub_eq_add_neg,
        div_neg, ← neg_add', abs_neg] at diff

      specialize diff x_properties.1 x_properties.2
      specialize max (a - |x|) --Sync up the neighbourhoods described in diff and max
      simp only [sub_sub_cancel_left, abs_neg, abs_abs, gt_iff_lt, sub_pos] at max
      specialize max x_lt_δ1
      /- We show (essentially) that the left-side limit is greater than |b|: this will contradict
      because by definition it must be zero-/
      --Limit is positive:
      have diff_pos : (f (a - |x|) - f a) / |x| < 0 := by
        apply div_neg_of_neg_of_pos
        · simpa
        · simpa
      --add b to both sides:
      have diff_b_gt_b : (f (a - |x|) - f a) / |x| + b < b := by simpa
      --The left-side limit is negative:
      have diff_b_pos : (f (a - |x|) - f a) / |x| + b < 0 := diff_b_gt_b.trans b_neg
      --The inside the LHS is negative, as is inside the RHS, so abs don't change anything:
      have diff_b_gt_b_norm : |-b| < |(f (a - |x|) - f a) / |x| + b| := by
        rw [← neg_pos] at b_neg
        rw [abs_of_neg diff_b_pos, abs_of_pos b_neg, neg_lt_neg_iff]
        exact diff_b_gt_b
      --Now we have our contradiction; we made sure that the LHS was less than |b|/2
      rw [abs_neg] at diff_b_gt_b_norm

      have bad : |b| / 2 > |b| := diff_b_gt_b_norm.trans diff
      --Finish it off:
      exact (good.not_lt bad).elim

    | inr b_pos => -- BM: I haven't changed this part as much
      specialize diff (|x|) --Similarly, we reach a contradiction when x>0

      have x_properties_pos : |x| ≠ 0 ∧ |(|x|) - 0| < δ2 := by
          constructor
          · norm_num
            exact x_nonzero
          · norm_num
            aesop

      specialize diff x_properties_pos.1 x_properties_pos.2
      specialize max (a + |x|) --Sync up the neighbourhoods described in diff and max
      simp only [add_sub_cancel_left, abs_abs] at max
      specialize max x_lt_δ1
      --Again, essentially the right-side limit has norm greater than |b|. Proceed like last time
      --Limit is negative:
      have diff_neg : ((f (a + |x|) - f a ) / |x|) < 0 := by
        rw[← neg_zero] at max
        apply GT.gt.lt at max
        rw[neg_lt] at max
        rw[neg_sub] at max
        apply LT.lt.gt
        rw[div_neg_iff]
        right
        constructor
        · exact max
        · aesop
      --subtract b from both sides:
      have diff_b_lt_b : ((f (a + |x|) - f a ) / |x|) - b < -b := by
        rw[← sub_lt_sub_iff_left b] at diff_neg
        norm_num at diff_neg
        apply neg_lt_neg at diff_neg
        norm_num at diff_neg
        exact diff_neg
      --Left limit is negative:
      have diff_b_neg : ((f (a + |x|) - f a ) / |x|) - b < 0 := by
        apply GT.gt.lt at b_pos
        apply neg_lt_neg at b_pos
        rw[neg_zero] at b_pos
        exact add_lt_of_lt_of_neg diff_neg b_pos
      --This time, norm flips the inequality
      have diff_b_gt_b_norm : |((f (a + |x|) - f a ) / |x|) - b| > |-b| := by
        rw[abs_of_neg diff_b_neg]
        simp
        rw[abs_of_pos b_pos]
        rw[lt_neg] at diff_b_lt_b
        norm_num at diff_b_lt_b
        exact diff_b_lt_b
      --Conclude as in the b<0 case
      rw[abs_neg] at diff_b_gt_b_norm
      apply GT.gt.lt at diff_b_gt_b_norm

      have bad : |b|/2 > |b| := by exact gt_trans diff diff_b_gt_b_norm

      apply LT.lt.not_lt at good
      apply GT.gt.lt at bad
      exact False.elim (good bad)
  done
