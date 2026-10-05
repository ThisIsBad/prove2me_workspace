import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain
import Definitions.Def_SennottDP_MarkovCost_Costs

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Proposition C.2.6, p. 301. Assume that the Markov chain with costs is `z`
standard. Then
(i) `S` decomposes into a positive recurrent class `R` containing `z` and a set `U = S − R` of
transient states;
(ii) the average cost `J_R` on `R` is finite;
(iii) `lim_{n→∞} J^{(n)}_i` exists and equals `J_R` for all `i ∈ S`. -/
theorem z_standard_average_cost {S : Type} [Countable S] (M : MC S) (C : S → ℝ≥0) (z : S)
    (hz : IsZStandard M C z) :
    ∃ R : Set S, IsPosRecClass M R ∧ z ∈ R ∧ (∀ i ∉ R, Transient M i) ∧
      classAvgCost M C R < ⊤ ∧
      ∀ i, Tendsto (fun n : ℕ => avgCostN M C n i) atTop (𝓝 (classAvgCost M C R)) := by sorry

end SennottDP.MarkovCost

