import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, Eq. (33) and following paragraph, p. 74:
the printed transfers split channel costs and make its unique optimum the
retailer's unique optimum for every `λ ∈ (0,1]`; the retailer's contracted cost at
each stock level is strictly increasing in `λ` ("the retailer's share of the cost increasing in
the parameter λ"). -/
theorem eq_33 (M : Model) :
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      (∀ s : ℝ, M.contractedRetailerCost lam s = lam * M.chainCost s ∧
        M.contractedSupplierCost lam s = (1 - lam) * M.chainCost s) ∧
      (∀ s : ℝ, StrictMonoOn (fun l => M.contractedRetailerCost l s) (Set.Ioc 0 1)) ∧
      ∃ so : ℝ, 0 < so ∧ M.F so = M.beta / (M.hr + M.beta) ∧
        IsMinOn M.chainCost Set.univ so ∧
        IsMinOn (M.contractedRetailerCost lam) Set.univ so ∧
        (∀ s : ℝ, IsMinOn M.chainCost Set.univ s → s = so) ∧
        (∀ s : ℝ, IsMinOn (M.contractedRetailerCost lam) Set.univ s → s = so) := by sorry

end CachonCoord.BaseStock

