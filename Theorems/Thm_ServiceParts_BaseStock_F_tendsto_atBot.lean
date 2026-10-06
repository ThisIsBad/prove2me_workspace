import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model
import Definitions.Def_ServiceParts_BaseStock_Recursion

open MeasureTheory Set Filter Topology

namespace ServiceParts.BaseStock

/-- Section 2.1, p. 19: if the order-up-to rule with a (finite) level s is optimal in the
n-period problem (n ≥ 2), then as w → −∞,
Fₙ(w) = c + α ∫₀^∞ f′ₙ(w − x) g(x) dx → (1 − α)c − bα, and this limit is negative. -/
theorem F_tendsto_atBot (M : Model) (n : ℕ) (hn : 2 ≤ n) (s : ℝ)
    (hs : M.IsOrderUpToOptimal n s) :
    Tendsto (M.F n) atBot (𝓝 ((1 - M.α) * M.c - M.b * M.α)) ∧
      (1 - M.α) * M.c - M.b * M.α < 0 := by sorry

end ServiceParts.BaseStock

