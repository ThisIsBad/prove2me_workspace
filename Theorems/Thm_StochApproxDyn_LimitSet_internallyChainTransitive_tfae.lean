import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence
import Definitions.Def_StochApproxDyn_LimitSet_Attractor

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- Proposition 5.3 (Benaïm 1999, p. 23), for a nonempty `Λ ⊂ M`. The following are equivalent:
(i) `Λ` is internally chain transitive; (ii) `Λ` is connected and internally chain recurrent;
(iii) `Λ` is a compact invariant set and `Φ|Λ` admits no proper attractor (every attractor of the
restricted semiflow is all of `Λ`). -/
theorem internallyChainTransitive_tfae {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (Λ : Set M) (hΛ : Λ.Nonempty) :
    List.TFAE
      [IsInternallyChainTransitive Φ Λ,
       IsConnected Λ ∧ IsInternallyChainRecurrent Φ Λ,
       IsCompact Λ ∧ ∃ h : IsInvariantSet Φ Λ,
         ∀ A : Set Λ, IsAttractor (restrictSemiflow Φ h) A → A = Set.univ] := by sorry

end StochApproxDyn.LimitSet

