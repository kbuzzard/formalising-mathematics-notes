/-
Formalising Mathematics
Imperial College London
MSc Pure Mathematics
Coursework 1
Author: Naomi Rosenberg
-/
--------------------------------------------------------------------------------------------------------------

/- **Goal:** The goal of this project is to define some basic notions from numerical analysis in order to
numerically solve initial value problems of the form

    dx/dt = f(t,x)  , t ∈ [0,T]
    x(0)  = x_0,

where f is (Lipschitz) continuous in t on [0,T] × ℝ.

We define the arguably simplest one-step method, the so-called explicit Euler method and prove some basic
results about it. -/

----------------------------------------------------------------------------------------------------------------

import Mathlib.Tactic -- Import all the tactics in Lean's maths library
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension -- Needed for a Lemma

set_option relaxedAutoImplicit true
set_option autoImplicit true

/- **SOME BASIC DEFINITIONS** -/

/-- Definition of closed intervals as a subset of ℝ. -/
def interval (a : ℝ) (b : ℝ): Set ℝ := {x : ℝ | a ≤ x ∧ x ≤ b}

/-- Definition of left open intervalsas a subset of ℝ. -/
def left_open_interval (a : ℝ) (b : ℝ): Set ℝ := {x : ℝ | a < x ∧ b ≤ x}

-- Introduction of variables used throughout the file
variable {T : ℝ}

/-- Definition of Lipschitz continuity in t on an interval [0,T] for functions ℝ → ℝ, mapping t ↦ f(t,x(t)),
  where f : ℝ × ℝ → ℝ, and x : ℝ → ℝ. -/
def lipschitz_continuous (f : ℝ × ℝ → ℝ) (T : ℝ) : Prop :=
  ∃ C > 0, ∀ t ∈ interval 0 T, ∀ a b : ℝ, abs (f (t, a) - f (t, b)) ≤ C * abs (a - b)

-- The namespace Set is opened in order to use the indicator function.
open Set

/-- Definition of the differential equation with continuous f. -/
def diff_eq (x : ℝ → ℝ) (f : ℝ × ℝ → ℝ) : Prop :=
  (∀ t ∈ interval 0 T, ContinuousAt (fun t => f (t,x t)) t) ∧
  (fun t => indicator (interval 0 T) (derivWithin x (interval 0 T)) t) =
   (fun t => indicator (interval 0 T) (fun t => f (t, x t)) t)

/-- By definition, a function x : ℝ → ℝ solves the initial value problem considered if and only if it
  satisfies ivp_sol. -/
def ivp_sol (f: ℝ × ℝ → ℝ)(x_0 : ℝ)(x : ℝ → ℝ) : Prop :=
  x 0 = x_0 ∧ diff_eq (T := T) x f

----------------------------------------------------------------------------------------------------------------
/- Note: The following definition is not used throughout the file. It is given as it might be useful for future
projects on in Lean since if the condition from the definition is satisfied, then there exists
a solution to the initial value problem considered. The definition is therefore useful when it comes to proving
statements about the existence of solutions to differential equations.-/
/-- Defintion of the initial value problem that is supposed to be approximated numerically.
  "ivp (f) (x_0)" assesses whether, for a given f and x_0, there exists an x which solves the initial value
  problem. -/
def ivp (f: ℝ × ℝ → ℝ)(x_0 : ℝ) : Prop :=
  ∃ x : ℝ → ℝ, x 0 = x_0 ∧ diff_eq (T := T) x f
----------------------------------------------------------------------------------------------------------------

/-- Definition of a general explicit one-step method. -/
def explicit_one_step_method (Φ : ℝ × ℝ × ℝ → ℝ) (Δt : ℝ) (x_0 : ℝ): ℕ → ℝ
  | 0 => x_0
  | k + 1 => explicit_one_step_method (Φ) (Δt) (x_0) k +
    Δt * Φ ((k : ℝ) * Δt, explicit_one_step_method (Φ) (Δt) (x_0) k, (Δt : ℝ))

/-- Definition of the truncation error of a numerical method. -/
noncomputable def truncation_error (x : ℝ → ℝ) (k : ℕ) (Φ : ℝ × ℝ × ℝ → ℝ) (Δt : ℝ) : ℝ :=
  (x (Δt *((k : ℝ) + (1 : ℝ))) - x (Δt*(k:ℝ))) / Δt - Φ ((k : ℝ) * Δt, x (Δt*k), Δt)

/-- Definition of consistency of a numerical method. -/
def is_consistent (Φ : ℝ × ℝ × ℝ → ℝ) (x_0 : ℝ) (f : ℝ × ℝ → ℝ) : Prop :=
  (∃ x : ℝ → ℝ, ((ivp_sol (T:=T) f x_0 x))) ∧ (∀ t ∈ interval 0 T, ∀ a : ℝ, Φ (t, a, 0) = f (t, a))

/-- Definition of stability of a numerical method. -/
def is_stable (Φ : ℝ × ℝ × ℝ → ℝ) : Prop :=
  ∃ C>0, ∃ h_0>0, ∀ t ∈ interval 0 T, ∀ a b: ℝ, ∀ Δt ∈ interval 0 h_0,
  abs (Φ (t, a , Δt) - Φ (t, b, Δt)) ≤ C * abs (a - b)

/-- Definition of the global error of a numerical method. -/
def global_error (Φ : ℝ × ℝ × ℝ → ℝ) (Δt : ℝ) (x_0 : ℝ) (k : ℕ) (x : ℝ → ℝ) : ℝ :=
  abs (explicit_one_step_method (Φ) (Δt) (x_0) k - x k * Δt)

----------------------------------------------------------------------------------------------------------------
-- Convergence

-- Adaptation of TendsTo definition from Section02reals/Sheet3.lean
/-- Definition stating when a function a : ℕ × ℝ → ℝ tends to t ∈ ℝ. -/
def TendsTo (a : ℕ × ℝ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

/-- Definition of convergence. -/
def is_convergent (Φ : ℝ × ℝ × ℝ → ℝ) (x_0 : ℝ) (x : ℝ → ℝ) (f: ℝ × ℝ → ℝ) : Prop :=
  TendsTo (fun (k,Δt) ↦ abs (global_error (Φ) (Δt) (x_0) (k) (x))) (0) ∧ ivp_sol (T:=T) f x_0 x
----------------------------------------------------------------------------------------------------------------
/- Dahlquist-Lax Theorem: A one-step method is convergent if and only if it is consistent and stable.
 This statement is a lemma in the proof of the main theorem. For now, I assume it to be true. I propose
 to work on  a proof for this statement in a future Lean project. -/
theorem dahlquist_lax_theorem (Φ : ℝ × ℝ × ℝ → ℝ) (x_0 : ℝ) (x : ℝ → ℝ) (f : ℝ × ℝ → ℝ):
  is_convergent (T := T) Φ x_0 x f ↔ (is_consistent (T := T) Φ x_0 f ∧ is_stable (T := T) Φ) := by
  sorry

----------------------------------------------------------------------------------------------------------------
/- Some statemets from the proof ot Dahlquist-Lax theorem which are needed for the proof of the order theorem.
 **In the theorems, the way they are stated below, we do not consider any additional conditions imposed by the**
 **Dahlquist-Lax Theorem. Therefore, the statements from this section do not hold in generality.**
 I decided to comment out the statement that are not used again throughout the file to avoid confusion.
 In this section, we make use of sSup, a definition of the supremum of a set, and IsBigO for Landau big O notation.
 These definitions were both suggested to me by Bhavik Mehta. -/

-- The namespace is Asymptotics is opened in order to work with Landau notation.
open Asymptotics

/- Remark: The follwing definitions are not intended to be added to MathLib, and therefore their descriptions
  are not self-explanatory. I intend to implement them in my proof of the Dahlquist-Lax theorem which I intend
  to approach in the future. -/

/-- Auxiliary definition used in the Proof of Dahlquist-Lax Theorem (1). -/
noncomputable def ω_1 (Δt : ℝ) (f : ℝ × ℝ → ℝ) (T : ℝ) (x : ℝ → ℝ) : ℝ :=
  sSup { y | ∃ s t, abs (t - s) ≤ Δt ∧
  (t ∈ interval 0 T) ∧ (s ∈ interval 0 T) ∧ y = abs (f (t, x t) - f (s, x s))}

-- /- In the proof of the Dahlquist-Lax Theorem, we show that ω_1 = O(Δt). -/
-- theorem lemma_ω_1 (f : ℝ × ℝ → ℝ) (T : ℝ) :
--   IsBigO (nhds 0) (fun d ↦ ω_1 d f T x) id := by
--   sorry

/-- Auxiliary definition used in the Proof of Dahlquist-Lax Theorem (2). -/
noncomputable def ω_2 (Δt : ℝ) (f : ℝ × ℝ → ℝ) (Φ : ℝ × ℝ × ℝ → ℝ) : ℝ :=
  sSup { y : ℝ | ∃ a : ℝ, ∃  t ∈ interval 0 T, ∃ h ∈ left_open_interval 0 Δt, y = abs (Φ (t, a, h) - f (t, a))}

-- /- In the proof of the Dahlquist-Lax Theorem, we show that ω_2 = 0. -/
-- theorem lemma_ω_2 (Δt : ℝ) (f : ℝ × ℝ → ℝ) (Φ : ℝ × ℝ × ℝ → ℝ):
--   ω_2 (Δt) (f) (Φ) (T := T) = (0 : ℝ) := by
--   sorry

/-- Auxiliary definition used in the Proof of Dahlquist-Lax Theorem (3). -/
noncomputable def ω_3 (Δt : ℝ) (f : ℝ × ℝ → ℝ) (Φ : ℝ × ℝ × ℝ → ℝ) (x : ℝ → ℝ) : ℝ :=
  ω_1 (Δt) (f) (T) (x) + ω_2 (Δt) (f) (Φ) (T := T)

/- In the proof of the Dahlquist-Lax Theorem, we show that the global error is O(Δt). This theorem only holds
  in the specific context of the proof of the Dahlquist-Lax Theorem given in the Lecture Notes, specified in my
  project report. -/
theorem lemma_ω_3 (f : ℝ × ℝ → ℝ) (Φ : ℝ × ℝ × ℝ → ℝ) (T : ℝ) :
  ∀ (k : ℕ), ((k*Δt) ≤ T) → ((IsBigO (nhds 0) (fun d ↦ global_error Φ d x_0 k x) id)) := by
  sorry

-- The namespace Set is opened in order to use the exp function.
open Real

-- /- To show the previous theorem, we probe the following bound of the gloval error. -/
-- theorem lemma_error (Φ : ℝ × ℝ × ℝ → ℝ) (Δt : ℝ) (x_0 : ℝ) (k : ℕ) (x : ℝ → ℝ) (T) :
--   ∀ (k : ℕ), (abs (global_error Φ Δt x_0 k x) ≤
--   exp (C * T) * abs (global_error Φ Δt x_0 0 x) +
--   ((exp (C*T) - 1) / (C)) * (ω_3 (T:=T) (Δt) (f) (Φ) (x)))
--   ∨ ((k*Δt) > T) := by
--   sorry

----------------------------------------------------------------------------------------------------------------

/-- Definition of explicit Euler method. -/
def explicit_euler (f : ℝ × ℝ → ℝ) (Δt : ℝ) (x_0 : ℝ) : ℕ → ℝ :=
  explicit_one_step_method (fun (t,x,Δt) => f (t, x) + 0*Δt) (Δt) (x_0)

/-- Definition checking if a method is an explicit Euler method. -/
def is_euler (f : ℝ × ℝ → ℝ) (x_0 : ℝ) (Φ : ℝ × ℝ × ℝ → ℝ) : Prop :=
  (∃ x : ℝ → ℝ, (ivp_sol (T := T) f x_0 x)) ∧
  (∀ t ∈ interval 0 T, ∀ a : ℝ, ∀ Δt ∈ interval 0 T, Φ (t,a,Δt) = f (t,a))

----------------------------------------------------------------------------------------------------------------
/- Main Theorem: Consider an initial value problem of the form introduced in the **Goal**.
  Then the explicit Euler scheme is convergent.-/
theorem main_theorem (f: ℝ × ℝ → ℝ) (x_0 : ℝ) (Φ : ℝ × ℝ × ℝ → ℝ) :
  is_euler (T:=T) (f) (x_0) (Φ) ∧ T>0 ∧ lipschitz_continuous f T→
  is_convergent (T:=T) (Φ) (x_0) (x) (f) := by

  intro h -- Hypothesis: (is_euler f x_0 Φ ∧ T > 0) ∧ (lipschitz_continuous f T)
  rw[dahlquist_lax_theorem] -- Change to goal to showing stability and consistency
  constructor -- Seperate the two goal from each other - create two separate goals
  -- Proof of Consistency
  · rw [is_consistent]
    rw [is_euler] at h
    constructor
    · cases' h with h_euler h_lipschitz
      cases' h_euler with h_ivp h_Φ_f
      apply h_ivp
    · rcases h with ⟨h1, h_T_pos, h_lipschitz⟩
      cases' h1 with h_ivp h_Φ_f
      intro t
      have zero_works: 0 ∈ interval 0 T := by
        rw[interval]
        norm_num
        change 0 < T at h_T_pos
        exact le_of_lt h_T_pos
      aesop
  -- Proof of Stability
  · rw [is_stable]
    rw [lipschitz_continuous] at h
    cases' h with h_euler h_lipschitz
    rcases h_lipschitz with ⟨h_T_pos, C, h_C_pos, h_lipschitz⟩
    use C
    constructor
    · apply h_C_pos
    · use T
      constructor
      · exact h_T_pos
      · rw[is_euler] at h_euler
        cases' h_euler with h_ivp h_Φ_f
        cases' h_ivp with x h_ivp
        aesop

----------------------------------------------------------------------------------------------------------------

/-- Definition of the order of a numerical method. -/
def of_order_p_method (x : ℝ → ℝ) (Φ : ℝ × ℝ × ℝ → ℝ) (p : ℕ) : Prop :=
  ∃ h_0 > 0, ∀ Δt ∈ left_open_interval 0 h_0, ∀ k ∈ {k : ℕ | k * (Δt) ≤ T}, ∃ C > 0,
  abs (truncation_error x k Φ Δt) ≤ C * (Δt)^(p : ℝ)

/-- Definition of the order of the global error. -/
def of_order_p_error (x : ℝ → ℝ) (k : ℕ) (Φ : ℝ × ℝ × ℝ → ℝ) (x_0 : ℝ) (p : ℕ) (Δt : ℝ) : Prop :=
  ((k * Δt) ≤ T) → ((IsBigO (nhds 0) (fun d ↦ global_error Φ d x_0 k x) (fun d ↦ d^p)))

----------------------------------------------------------------------------------------------------------------

/- With the same conditions as above, the global error is of order one. -/
theorem order_theorem_1 (f: ℝ × ℝ → ℝ) (x_0 : ℝ) (Δt : ℝ) (Φ : ℝ × ℝ × ℝ → ℝ) :
  is_euler (T:=T) (f) (x_0) (Φ) ∧ T>0 ∧
  lipschitz_continuous f T → of_order_p_error (T := T) (x) (k) (Φ) (x_0) (1) (Δt) := by

  intro h
  cases' h with h_euler h_rest
  cases' h_rest with h_T_pos h_lipschitz

  -- Apply lemma_ω_3
  have h_ω_3 : ∀ (k : ℕ), ((k*Δt) ≤ T) → ((IsBigO (nhds 0) (fun d ↦ global_error Φ d x_0 k x) id)) := by
    apply lemma_ω_3
    exact f

  -- Combine results to prove of_order_p_error
  rw [of_order_p_error]

  simp only [pow_one]

  have h_fun_eq_id : ((fun d => d) : ℝ → ℝ) = (id : ℝ → ℝ) := by
    rfl

  rw [h_fun_eq_id]

  aesop

----------------------------------------------------------------------------------------------------------------

/- This part of the proof was given to me by Bhavik Mehta.
  The first theorem is known as regularity theorem. It states that if a function x is differentiable and its
  derivative is n times continuously differentiable, then x is (n+1) times continuously differentiable.
  The second theorem is an application of the regularity theorem to the functions as above, but multiplied by the
  characteristic function of an interval [0,T]. -/

theorem regularity_theorem {T : ℝ} (hT : 0 < T) {x : ℝ → ℝ} (n : ℕ)
    (hn : ContDiffOn ℝ n (fun t ↦ derivWithin x (Icc 0 T) t) (Icc 0 T))
    (hx : DifferentiableOn ℝ x (Icc 0 T)) :
    ContDiffOn ℝ (n + 1) x (Icc 0 T) := by
  rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)]
  exact ⟨hx, by simp, hn⟩

theorem regularity_theorem_on_indicator {T : ℝ} (hT : 0 < T) {x : ℝ → ℝ}
    (hx : DifferentiableOn ℝ (fun t => (Icc 0 T).indicator x t) (Icc 0 T)) :
    ∀ (n : ℕ),
      ContDiffOn ℝ n (fun t => indicator (Icc 0 T) (derivWithin x (Icc 0 T)) t) (Icc 0 T) →
      ContDiffOn ℝ (n + 1) (fun t => indicator (Icc 0 T) x t) (Icc 0 T) := by
  intro n hn
  replace hn : ContDiffOn ℝ n (fun t ↦ derivWithin x (Icc 0 T) t) (Icc 0 T) := by
    apply ContDiffOn.congr hn
    intro i hi
    simp [indicator_apply, hi]
  suffices ContDiffOn ℝ (n + 1) x (Icc 0 T) by
    apply this.congr
    intro t ht
    simp [indicator_apply, ht]
  replace hx : DifferentiableOn ℝ x (Icc 0 T) := by
    apply DifferentiableOn.congr hx
    intro i hi
    simp [indicator_apply, hi]
  exact regularity_theorem hT _ hn hx

----------------------------------------------------------------------------------------------------------------
/- The following theorem allows us to apply the theory developed above to intervals using the
"interval"-definition instead of the "Icc" definition from the set namespace. -/

/- The "interval" definition is the same as the "Icc" defintion. -/
theorem equivalent_interval_definitions (a b : ℝ) : Icc a b = interval a b := by rfl

----------------------------------------------------------------------------------------------------------------

/- A special case of the Regularity Theorem: If f is once continuously differentiable, then x is twice
continuously differentiable. -/
theorem f_C1_implies_x_C2 (f: ℝ × ℝ → ℝ) (T := T) (x : ℝ → ℝ) (x_0 : ℝ)
  (hx : DifferentiableOn ℝ (fun t => (interval 0 T).indicator x t) (interval 0 T)) (h_T_pos : T > 0) :
  ContDiffOn ℝ 1 (fun t => indicator (interval 0 T) (fun t => f (t, x t)) t) (interval 0 T) ∧
  ivp_sol (T := T) (f) (x_0) (x) → ContDiffOn ℝ 2 (fun t => indicator (interval 0 T) (x) t) (interval 0 T) := by

  intro h
  cases' h with h_cont_diff h_ivp

  have h_derivx_cont_diff :
    ContDiffOn ℝ 1 (fun t => indicator (interval 0 T) (derivWithin x (interval 0 T)) t) (interval 0 T) := by

    change (ContDiffOn ℝ 1 (fun t => indicator (interval 0 T) (fun t => f (t, x t)) t) (interval 0 T))
    at h_cont_diff
    rw[ContDiffOn] at h_cont_diff
    rw[ContDiffOn]
    rw[ivp_sol] at h_ivp
    cases' h_ivp with h_init h_diff_eq

    rw[_root_.diff_eq] at h_diff_eq
    cases' h_diff_eq with h_f_cont h_derivx_equals_f

    rw [h_derivx_equals_f]

    exact h_cont_diff

  have reg_thm : (ContDiffOn ℝ (2) (fun t => indicator (interval 0 T) (x) t) (interval 0 T)) := by
    apply regularity_theorem_on_indicator
    · exact h_T_pos
    · exact hx
    · rw [equivalent_interval_definitions]
      aesop

  aesop


/- With the same conditions as above, and the additional condition that f is continuously differentiable,
the global error is of order one. -/
theorem order_theorem_contdiff (f: ℝ × ℝ → ℝ)(x_0 : ℝ)(Δt : ℝ)(Φ : ℝ × ℝ × ℝ → ℝ) :
  is_euler (T:=T) (f) (x_0) (Φ) ∧ T>0 ∧ lipschitz_continuous (T:=T) f ∧
  DifferentiableAt ℝ (fun t => f (t,x t)) t ∧ ContinuousAt (derivWithin (fun t => f (t,x t)) (interval 0 T)) t →
  of_order_p_method (T:=T) (x) (Φ) (1) := by
  sorry
