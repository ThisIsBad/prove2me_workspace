import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- Theorem 5.5 (Benaïm 1999, p. 23): if `M` is a (nonempty) compact metric space, the chain
recurrent set `R(Φ)` of a semiflow `Φ` on `M` is internally chain recurrent. -/
theorem chainRecurrentSet_isInternallyChainRecurrent {M : Type*} [MetricSpace M]
    [CompactSpace M] [Nonempty M] (Φ : Flow ℝ≥0 M) :
    IsInternallyChainRecurrent Φ (chainRecurrentSet Φ) := by sorry

end StochApproxDyn.LimitSet

