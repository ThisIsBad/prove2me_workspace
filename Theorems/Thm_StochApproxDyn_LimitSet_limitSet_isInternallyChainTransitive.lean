import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- Theorem 5.7 (i) (Benaïm 1999, p. 24): let `Φ` be a semiflow on an arbitrary metric space `M`
and `X : ℝ₊ → M` a precompact asymptotic pseudotrajectory of `Φ`. Then its limit set
`L(X) = ⋂_{t ≥ 0} closure (X([t, ∞)))` is internally chain transitive. -/
theorem limitSet_isInternallyChainTransitive {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (X : ℝ≥0 → M) (hX : IsAsymptoticPseudotrajectory Φ X)
    (hpre : IsCompact (closure (Set.range X))) :
    IsInternallyChainTransitive Φ (limitSet X) := by sorry

end StochApproxDyn.LimitSet

