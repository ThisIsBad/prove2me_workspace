import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain
import Definitions.Def_SennottDP_MarkovCost_Costs

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Proposition C.2.1, p. 298. Let `R` be a positive recurrent class and
`J_R = ∑_{j ∈ R} π_j C(j)` (finite or infinite).
(i) For `i ∈ R`, `lim_{n→∞} J^{(n)}_i` exists and equals `J_R`.
(ii) For `i ∈ R`, `J_R = c_{ii}/m_{ii}`.
(iii) `J_R = ∑_{j ∈ R} π_j E[C(X_n) | X_0 = j]` for `n ≥ 0`. -/
theorem class_average_cost {S : Type} [Countable S] (M : MC S) (C : S → ℝ≥0) (R : Set S)
    (hR : IsPosRecClass M R) :
    (∀ i ∈ R, Tendsto (fun n : ℕ => avgCostN M C n i) atTop (𝓝 (classAvgCost M C R))) ∧
    (∀ i ∈ R, classAvgCost M C R = passageCost M C {i} i / meanPassage M {i} i) ∧
    (∀ n : ℕ, classAvgCost M C R =
      ∑' j : R, steadyState M j * ∑' k, nStep M n j k * (C k : ℝ≥0∞)) := by sorry

end SennottDP.MarkovCost

