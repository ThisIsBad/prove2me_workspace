import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network
import Definitions.Def_FordFulkerson58_ArcChain_LP
import Definitions.Def_FordFulkerson58_ArcChain_Labeling

namespace FordFulkerson58.ArcChain

/-- §3, p. 1779: if the simplex multipliers of a feasible basis are non-negative and every commodity
chain has length `∑_r α_r a_rs ≥ 1` (the arc lengths being the multipliers), the basis is optimal: no
feasible flow has a larger total than the basic solution. -/
theorem basis_optimal_of_chainLength_ge_one {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] (N : Network V E ι)
    (β : E → Col N ⊕ E) (hβ : IsUnit (basisMatrix N β).det)
    (z : Col N ⊕ E → ℝ) (hz : IsBasicFeasibleSolution N β z)
    (α : E → ℝ) (h4 : IsSimplexMultiplier N β α)
    (hα : ∀ r, 0 ≤ α r) (hlen : ∀ s : Col N, (1 : ℝ) ≤ chainLength α s.1.2) :
    ∀ (x : Col N → ℝ) (y : E → ℝ), Feasible N x y → ∑ s, x s ≤ ∑ s, z (Sum.inl s) := by sorry

end FordFulkerson58.ArcChain

