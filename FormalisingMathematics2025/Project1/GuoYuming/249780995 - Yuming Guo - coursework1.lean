import Mathlib.Tactic -- imports all the lean tactics
import Mathlib.MeasureTheory.Measure.Hausdorff -- imports the Hausdorff measure
import Mathlib.Topology.MetricSpace.HausdorffDimension -- imports the Hausdorff dimension
import Mathlib.Order.CompletePartialOrder -- imports the complete partial order

open ENNReal MeasureTheory

namespace coursework1 -- sets up the namespace

/-
In coursework 1, I attempt to formalise the proof the Mass Distribution Principle,
which can be described as follows:
Let μ be a mass distribution on F, any subset of a space, and suppose that for
some s there exist numbers c > 0 and ε > 0, such that
        μ(U) ≤ c|U|^s (*)
for all sets U with |U| ≤ ε. Then H^s(F) ≥ μ(F)/c.
Then as a direct consequence, we have dim_H(F) ≥ s.

Informal Proof:
If {U_i} is any cover of F, then
  0 < μ(F) ≤ μ(∪U_i) ≤ Σμ(U_i) ≤ cΣ|U_i|^s, by properties of measure and (*).
Taking infima across all such covers, H_δ^s(F) ≥ μ(F)/c for small enough δ, hence
H^s(F) ≥ μ(F)/c.
-/

/- Let X be a measurable space; c and ε positive real numbers (formatted as NNReals), s a non-neg
real number, and μ a mass distribution on F. -/
variable {X : Type*} [MeasurableSpace X] {ε : ENNReal} {c : NNReal} (s : ℝ) (μ : Measure X)

/- Let X be a metric space, Borel space and measure space. Let F be a subset of X. We have that for
all sets U in X, if |U| ≤ ε, then μ(U) ≤ c|U|^s. Then the mass distribution principle states that the
s-dimensional Hausdorff measure of F is greater or equal to μ(F) / c. -/
theorem mass_dist_principle [MetricSpace X] [BorelSpace X] [MeasureSpace X] (hε : 0 < ε) (F : Set X)
    (hs: 0 < s) :
    (∀ U : Set X, EMetric.diam U ≤ ε → μ U ≤ c * EMetric.diam U ^ s) → μ F / c ≤ μH[s] F := by
  intro hμ -- First we introduce the hypothesis that μ(U) ≤ c|U|^s for all U with |U| ≤ ε
  rw [Measure.hausdorffMeasure_apply] /- Then we apply the definition of s-dimensional Hausdorff
  measure -/
  apply le_iSup₂_of_le ε hε /- This is the proof that the lower bound of function value implies
  lower bound of indexed supremum in complete lattices (which ENNReal is) with double indices -/
  apply le_iInf₂ /- This is the proof that, if an element is less than or equal to every element in f,
  then it is also less than or equal to the infimum of f -/
  intro U hU -- Now we introduce the cover U of F
  apply le_iInf
  intro hU' -- We introduce the hypothesis that each component of the cover has diameter ≤ ε

  -- Here we prove the string of inequalities 0 < μ(F) ≤ μ(∪U_i) ≤ Σμ(U_i) ≤ cΣ|U_i|^s
  have h1 : μ F ≤ c * ∑' n, EMetric.diam (U n) ^ s := by
    -- Let Ui be a covering of F, with each U_i being one of its components. Then μ(F) ≤ μ(⋃U_i)
    have h1a : μ F ≤ μ (⋃ n, U n) := by
      exact measure_mono hU -- This is the proof that if A ⊆ B, then μ(A) ≤ μ(B)

    -- Now we prove that μ(∪U_i) ≤ ∑μ(U_i)
    have h1b : μ (⋃ n, U n) ≤ ∑' n, μ (U n) := by
      exact measure_iUnion_le U /- This is the proof that the measure of a countable union of sets
      is less than or equal to the sum of the measures of the individual sets. -/

    -- Now we prove that ∑μ(U_i) ≤ c∑|U_i|^s, given that μ(U) ≤ c|U|^s for all sets U, and that
    -- each |U_i| ≤ ε.
    have h1c : ∑' n, μ (U n) ≤ c * ∑' n, EMetric.diam (U n) ^ s := by
      rw [← @ENNReal.tsum_mul_left] /- This is the proof that multiplication in the left preserves
      infinite sums in ENNReals. -/
      exact ENNReal.tsum_le_tsum fun a => hμ (U a) (hU' a) /- This is the proof that for two
      infinite sums ∑ a and ∑ b, if a ≤ b for every term then ∑ a ≤ ∑ b. -/

    exact le_implies_le_of_le_of_le h1a h1c h1b -- Finally we complete the chain using transitivity

  -- Now we can divide both sides by c
  have h2 : μ F / c ≤ ∑' n, EMetric.diam (U n) ^ s := by
    exact div_le_of_le_mul' h1

  /- Now we prove that the sum of the sth powers of the diameters of the components of the cover is
  less than or equal to the sum of the supremums of the sth powers of the diameters of the components -/
  have h3 : ∑' (n : ℕ), EMetric.diam (U n) ^ s ≤ ∑' (n : ℕ), ⨆ (_ : (U n).Nonempty),
      EMetric.diam (U n) ^ s := by
    gcongr with n /- The generalised congruence tactic reduces a relational goal to relational subgoals
    between the differinginputs to the pattern. -/
    if hNE : (U n).Nonempty then
    · simp [hNE] /- If the component is nonempty, then the definition of supremum automatically
      preserves the inequality -/
    -- However, if the component is empty:
    else
    · rw [Set.not_nonempty_iff_eq_empty] at hNE -- First we convert the 'not-nonempty' hypothesis to empty
      simp [hNE] -- This then simply converts the goal to 0 < s
      exact hs -- Which is exactly what we have

  -- Then the result follows by the transitivity of inequalities
  exact Preorder.le_trans (μ F / ↑c) (∑' (n : ℕ), EMetric.diam (U n) ^ s)
    (∑' (n : ℕ), ⨆ (_ : (U n).Nonempty), EMetric.diam (U n) ^ s) h2 h3



/- Then as a direct consequence, we have dim_H(F) ≥ s. Note that here we have to convert dimH
from ENNReal to NNReal to allow for the comparison with s. -/
theorem mass_dist_principle_dimH [MetricSpace X] [BorelSpace X] [MeasureSpace X]
    (F : Set X) (hμ1 : μ F = 1) (hε : 0 < ε) (hs : 0 < s)
    (hμ : ∀ U : Set X, EMetric.diam U ≤ ε → μ U ≤ c * EMetric.diam U ^ s): s.toNNReal ≤ dimH F := by
  -- First we establish the trivial result that μ(F) / c > 0
  have h1 : 0 < μ F / c := by
    rw [hμ1]
    norm_num

  -- Now we apply the mass distribution principle to get H^s(F) ≥ μ(F) / c
  have h2 : μ F / c ≤ μH[s.toNNReal] F := by
    have h2a := mass_dist_principle s μ hε F hs hμ
    simp only [Real.coe_toNNReal', hs, sup_of_le_left, ge_iff_le]
    rw [max_eq_left_of_lt hs]
    exact h2a

  /- This then implies that H^s(F) > 0. Here we use H^s(F) ≠ 0 since that is the required
  input for the theorem proving dimH(F) ≥ s in mathlib -/
  have h3 : μH[s.toNNReal] F ≠ 0 := by
    have h3a : 0 < μH[s.toNNReal] F := by
      exact lt_of_lt_of_le h1 h2 -- By transitivity of inequalities
    apply ne_of_gt at h3a -- By definition of inequality
    exact h3a
  -- Therefore we get that dimH(F) ≥ s
  exact le_dimH_of_hausdorffMeasure_ne_zero h3 -- The proof that if H^s(F) ≠ 0, then dimH(F) ≥ s

end coursework1 -- closes the namespace
