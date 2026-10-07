import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, Eq. (32) and the two parameter identities,
p. 74: the retailer's cost after the supplier-to-retailer transfer. -/
theorem eq_32 (M : Model) :
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      (∀ s : ℝ, M.contractedRetailerCost lam s =
        (M.br - M.tB lam) * (M.meanDemand - s) +
          (M.hr + M.br - M.tI lam - M.tB lam) * M.I s) ∧
      M.br - M.tB lam = lam * M.beta ∧
      0 < M.br - M.tB lam ∧
      M.hr + M.br - M.tI lam - M.tB lam = lam * (M.hr + M.beta) ∧
      0 < M.hr + M.br - M.tI lam - M.tB lam := by sorry

end CachonCoord.BaseStock

