import Mathlib.Tactic
import Mathlib.Init

/-! In this document we define what it means for a real-valued function to be differentiable,
and prove that at a local maximum, if the derivative of a function exists, it must vanish.
Submitted as the first coursework for 'Formalising Mathematics 2025' by Killian Burke -/

/-! Definitions -/

/-- For 'f' a real-valued function, encodes 'lim_x→a f(x) = b' -/
def LimFun_to (f : ℝ → ℝ) (a : ℝ) (b : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, x ≠ a ∧ |x - a| < δ → |f x - b| < ε
/-- 'f' is differentiable at 'a' with derivative 'b' when evaluated at 'a' -/
def MyDifferentiableAt (f : ℝ → ℝ) (a : ℝ) (b : ℝ ) : Prop :=
  LimFun_to (fun h => ((f (a + h) - f a ) / h)) 0 b
/-- 'a' is a local maximum of 'f' -/
def CritPoint_max (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ ε > 0, ∀ x : ℝ, |x-a| < ε → f a - f x > 0

/-! The Theorem -/

/-- If 'f' is differentiable at its local maximum 'a',
then the derivative evaluated at 'a' must be '0' -/
theorem Max_is_stationary (f : ℝ → ℝ) (a : ℝ) :
    CritPoint_max f a ∧ (∃ b : ℝ, MyDifferentiableAt f a b) → MyDifferentiableAt f a 0 := by
--Unfolding definitions:
  rintro ⟨a_max, b_diff⟩
  rcases b_diff with ⟨b, diff⟩
  unfold MyDifferentiableAt LimFun_to at diff --Not necessary, but helps with readability
  unfold CritPoint_max at a_max
  rcases a_max with ⟨δ1, max⟩
--Split into 3 cases: b>0, b<0, or b=0
  have bcases : b = 0 ∨ b ≠ 0 := by exact eq_or_ne b 0
  cases bcases with
  | inl b_zero => --Obviously true if b is 0; this could have been done at the VERY start
    rw[b_zero] at diff
    exact diff

  | inr b_nonzero => --When b ≠ 0
    specialize diff (|b|/2) --This ε will lead to a contradiction later on

    have b_half : |b|/2 > 0 := by --Needed to satisfy conditions on ε
      refine half_pos ?_
      exact abs_pos.mpr b_nonzero
    --Peel off the quantifiers:
    specialize diff b_half
    rcases diff with ⟨δ2, diff⟩
    let δ := min δ1 δ2 --Taking the minimum allows the use of diff and max at the same time
    rcases max with ⟨δ1_pos, max⟩
    rcases diff with ⟨δ2_pos, diff⟩

    have δ_pos : δ > 0 := by exact lt_min δ1_pos δ2_pos

    intro ε1 ε1_pos
    use δ, δ_pos
    intro x x_properties
    /- ^Really we shouldn't need to touch the goal at all, but I want to grab the 'x'
    inside because it already has all the properties I need without defining them again -/
    rcases x_properties with ⟨x_nonzero, x_lt_δ⟩
    norm_num at x_lt_δ

    have x_properties : x ≠ 0 ∧ |x - 0| < δ2 := by
      constructor
      · exact x_nonzero
      · norm_num
        aesop --aesop is great for shorcutting transitivity of '<'(among other things)

    have x_lt_δ1 : |x| < δ1 := by --Use this in both cases
      have δ_lt_δ1 : δ ≤ δ1 := by exact min_le_left δ1 δ2
      exact gt_of_ge_of_gt δ_lt_δ1 x_lt_δ

    have good : |b|/2 < |b| := by --we will contradict this
      refine div_two_lt_of_pos ?_
      exact abs_pos.mpr b_nonzero

    have b_neg_pos : b < 0 ∨ b > 0 := by exact lt_or_gt_of_ne b_nonzero --split b

    cases b_neg_pos with  --Check b<0 and b>0
    | inl b_neg =>
      specialize diff (-|x|) --Contradiction for negative x

      have x_properties_neg : -|x| ≠ 0 ∧ |-|x| - 0| < δ2 := by
        constructor
        · norm_num
          exact x_nonzero
        · norm_num
          aesop

      specialize diff x_properties_neg
      specialize max (a+-|x|) --Sync up the neighbourhoods described in diff and max
      simp only [add_sub_cancel_left, abs_neg, abs_abs] at max
      specialize max x_lt_δ1
      /- We show (essentially) that the left-side limit is greater than |b|: this will contradict
      because by definition it must be zero-/
      --Limit is positive:
      have diff_pos : ((f (a + -|x|) - f a ) / -|x|) > 0 := by
        rw[← neg_zero] at max
        apply GT.gt.lt at max
        rw[neg_lt] at max
        rw[neg_sub] at max
        apply LT.lt.gt
        rw[div_pos_iff]
        right
        constructor
        · exact max
        · aesop
      --subtract b from both sides:
      have diff_b_gt_b : ((f (a + -|x|) - f a ) / -|x|) - b > -b := by
        norm_num
        exact diff_pos
      --The left-side limit is positive:
      have diff_b_pos : ((f (a + -|x|) - f a ) / -|x|) - b > 0 := by
        apply neg_lt_neg at b_neg
        rw[neg_zero] at b_neg
        apply LT.lt.gt at b_neg
        exact add_pos diff_pos b_neg
      --The inside the LHS is positive, as is indide the RHS, so abs don't change anything:
      have diff_b_gt_b_norm : |((f (a + -|x|) - f a ) / -|x|) - b| > |-b| := by
        rw[abs_of_pos diff_b_pos]
        rw[← neg_pos] at b_neg
        rw[abs_of_pos b_neg]
        exact diff_b_gt_b
      --Now we have our contradiction; we made sure that the LHS was less than |b|/2
      rw[abs_neg] at diff_b_gt_b_norm
      apply GT.gt.lt at diff_b_gt_b_norm

      have bad : |b|/2 > |b| := by exact gt_trans diff diff_b_gt_b_norm
      --Finish it off:
      apply LT.lt.not_lt at good
      apply GT.gt.lt at bad
      exact False.elim (good bad)

    | inr b_pos =>
      specialize diff (|x|) --Similarly, we reach a contradiction when x>0

      have x_properties_pos : |x| ≠ 0 ∧ |(|x|) - 0| < δ2 := by
          constructor
          · norm_num
            exact x_nonzero
          · norm_num
            aesop

      specialize diff x_properties_pos
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
