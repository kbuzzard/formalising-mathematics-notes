import FormalisingMathematics2025.Project1.JamesHarry.CauchySchwarz
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic

variable {F : Type*}

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {f : F →  ℝ} {d : F} {x : F}

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

def directional_derivative (f : F → ℝ) (x : F) (d : F) : ℝ :=
  (fderiv ℝ f x) d

lemma directional_derivative_eq_inner_product:
    directional_derivative f x d = ⟪gradient f x, d⟫ :=
  InnerProductSpace.toDual_symm_apply.symm


lemma directional_derivative_lower_bound (hd: ‖d‖ = 1) :
    - ‖gradient f x‖ ≤ directional_derivative f x d := by
  rw [directional_derivative_eq_inner_product]
  have h1 : |⟪gradient f x, d⟫| ≤ ‖gradient f x‖ * ‖d‖ := abs_cauchy_schwarz (gradient f x) d
  simp only [hd, mul_one] at h1
  exact neg_le_of_abs_le h1

/- The unit vector in the direction -∇f(x) where ∇f(x)≠ 0 is the direction of steepest
local descent.-/
theorem minus_the_gradient_at_x_is_the_direction_of_steepest_local_descent
    (hx : gradient f x ≠ 0) (hd : ‖d‖ = 1) :
    directional_derivative f x ((-1 / ‖gradient f x‖) • gradient f x) ≤
      directional_derivative f x d := by
  rw [directional_derivative_eq_inner_product]

  have h1 : ⟪gradient f x, (-1 / ‖gradient f x‖) • gradient f x⟫ = -‖gradient f x‖ := by
    simp only [inner_smul_left, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [norm_ne_zero_iff]
    exact pow_two ‖gradient f x‖

  rw [h1]
  exact directional_derivative_lower_bound hd
