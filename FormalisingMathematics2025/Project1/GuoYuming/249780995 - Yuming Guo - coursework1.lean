import Mathlib.Tactic -- imports all the lean tactics
import Mathlib.MeasureTheory.Measure.Hausdorff -- imports the Hausdorff measure
import Mathlib.Topology.MetricSpace.HausdorffDimension -- imports the Hausdorff dimension
import Mathlib.Order.CompletePartialOrder -- imports the complete partial order

open ENNReal MeasureTheory
open EMetric

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
theorem mass_dist_principle [MetricSpace X] [BorelSpace X] (hε : 0 < ε) (F : Set X)
    (hs : 0 < s) (hμ : ∀ U : Set X, diam U ≤ ε → μ U ≤ c * diam U ^ s) : μ F / c ≤ μH[s] F := by
  rw [Measure.hausdorffMeasure_apply] /- Then we apply the definition of s-dimensional Hausdorff
  measure -/
  apply le_iSup₂_of_le ε hε /- This is the proof that the lower bound of function value implies
  lower bound of indexed supremum in complete lattices (which ENNReal is) with double indices -/
  refine le_iInf₂ fun U hU => ?_
  /- This is the proof that, if an element is less than or equal to every element in f,
  then it is also less than or equal to the infimum of f -/
  refine le_iInf fun hU' => ?_

  -- Here we prove the string of inequalities 0 < μ(F) ≤ μ(∪U_i) ≤ Σμ(U_i) ≤ cΣ|U_i|^s
  have h1 : μ F ≤ c * ∑' n, diam (U n) ^ s := calc
    _ ≤ μ (⋃ n, U n) := measure_mono hU
    _ ≤ ∑' n, μ (U n) := measure_iUnion_le U
    _ ≤ c * ∑' n, diam (U n) ^ s := by
        rw [← ENNReal.tsum_mul_left]
        exact ENNReal.tsum_le_tsum fun a => hμ _ (hU' a)

  -- Now we can divide both sides by c
  have h2 : μ F / c ≤ ∑' n, diam (U n) ^ s := div_le_of_le_mul' h1

  /- Now we prove that the sum of the sth powers of the diameters of the components of the cover is
  less than or equal to the sum of the supremums of the sth powers of the diameters of the
  components -/
  have h3 : ∑' (n : ℕ), diam (U n) ^ s ≤ ∑' (n : ℕ), ⨆ (_ : (U n).Nonempty), diam (U n) ^ s := by
    gcongr with n /- The generalised congruence tactic reduces a relational goal to relational
    subgoals between the differinginputs to the pattern. -/
    -- BM: ^ damn I wonder where you learnt that
    rcases (U n).eq_empty_or_nonempty with hE | hNE
    -- However, if the component is empty:
    · simpa [hE] -- This then simply converts the goal to 0 < s
    · simp [hNE] /- If the component is nonempty, then the definition of supremum automatically
      preserves the inequality -/

  -- Then the result follows by the transitivity of inequalities
  exact le_trans h2 h3


/- Then as a direct consequence, we have dim_H(F) ≥ s. Note that here we have to convert dimH
from ENNReal to NNReal to allow for the comparison with s. -/
theorem mass_dist_principle_dimH [MetricSpace X] [BorelSpace X]
    (F : Set X) (hμ1 : μ F ≠ 0) (hε : 0 < ε) (hs : 0 ≤ s)
    (hμ : ∀ U : Set X, diam U ≤ ε → μ U ≤ c * diam U ^ s) : s.toNNReal ≤ dimH F := by
  obtain rfl | hs' := hs.eq_or_lt
  · simp
  -- First we establish the trivial result that μ(F) / c > 0
  have h1 : 0 < μ F / c := ENNReal.div_pos hμ1 (by simp)

  -- Now we apply the mass distribution principle to get H^s(F) ≥ μ(F) / c
  have h2 : μ F / c ≤ μH[s.toNNReal] F := by simpa [hs] using mass_dist_principle s μ hε F hs' hμ

  /- This then implies that H^s(F) > 0. Here we use H^s(F) ≠ 0 since that is the required
  input for the theorem proving dimH(F) ≥ s in mathlib -/
  have h3 : μH[s.toNNReal] F ≠ 0 := (h1.trans_le h2).ne'
  -- Therefore we get that dimH(F) ≥ s
  exact le_dimH_of_hausdorffMeasure_ne_zero h3 -- The proof that if H^s(F) ≠ 0, then dimH(F) ≥ s

-- BM: I'd probably make s an NNReal throughout...

end coursework1 -- closes the namespace
