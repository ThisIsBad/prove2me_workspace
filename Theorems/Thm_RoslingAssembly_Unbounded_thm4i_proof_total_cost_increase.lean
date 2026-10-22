import Mathlib
import Definitions.Def_RoslingAssembly_Unbounded_Model
import Definitions.Def_RoslingAssembly_Unbounded_Perturb

namespace RoslingAssembly.Unbounded

open MeasureTheory

/-- Proof of Theorem 4(i), p. 578, "the total cost increase": for a non-end item `i ≥ 2` and a
measurable feasible policy `π` with real cost `J`, the policy with `δ ≥ 0` extra units of the
subsystem `{i} ∪ B(i)` has real cost
`J + δ α^{M_m − M_i} α^{l_i} (h_i + ∑_{k ∈ B(i)} h_k α^{−(M_{s(k)} − M_{s(i)})}) / (1 − α)`,
where `M_m = Mmax i`; the factor `α^{M_m − M_i}` discounts the paper's increase, capitalized to
period `M_m − M_i + 1`, back to period 1. -/
theorem thm4i_proof_total_cost_increase (S : Model) (x0 : ℕ → ℕ → ℝ)
    (hT : S.IsTree) (hI : S.IsIndexed) [IsProbabilityMeasure S.ν] (hD : S.DemandStanding)
    (hα0 : 0 < S.α) (hα1 : S.α < 1) (hx0 : S.WellFormed x0)
    (i : ℕ) (hi : i ∈ Finset.Icc 2 S.N) (δ : ℝ) (hδ : 0 ≤ δ)
    (π : RoslingAssembly.SeriesEquiv.Policy) (hπm : IsMeasurablePolicy π) (hπ : S.Feasible x0 π)
    (J : ℝ) (hJ : S.cost π = (J : EReal)) :
    S.cost (S.perturb π i δ) =
      ((J + δ * S.α ^ (S.Mmax i - S.M i) * S.α ^ S.l i *
          (S.h i + ∑ k ∈ S.B i,
            S.h k * S.α ^ (-((S.M (S.succ k) : ℤ) - (S.M (S.succ i) : ℤ)))) / (1 - S.α) : ℝ) :
        EReal) := by sorry

end RoslingAssembly.Unbounded

