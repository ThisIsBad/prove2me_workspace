import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- Corollary 5.6 (Benaïm 1999, p. 24): for `x` in a (not necessarily compact) metric space `M`,
if the forward orbit `γ⁺(x) = {Φ_t(x) : t ≥ 0}` has compact closure, then the omega limit set
`ω(x)` is internally chain transitive. -/
theorem omegaLimitSet_isInternallyChainTransitive {M : Type*} [MetricSpace M]
    (Φ : Flow ℝ≥0 M) (x : M) (hx : IsCompact (closure (Set.range fun t : ℝ≥0 => Φ t x))) :
    IsInternallyChainTransitive Φ (omegaLimitSet Φ x) := by sorry

end StochApproxDyn.LimitSet

