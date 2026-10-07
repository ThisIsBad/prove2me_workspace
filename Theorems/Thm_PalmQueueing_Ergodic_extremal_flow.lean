import Mathlib
import Definitions.Def_PalmQueueing_Ergodic_DiscreteFlow

/-!
# Theorem 1.6.5: the extremal characterization of continuous ergodic flows (§1.6.1, p.50)
-/

namespace PalmQueueing.Ergodic

open MeasureTheory
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 1.6.5 (Extremal property of ergodic flows)** (p.50). `(P, {θ_t})` is ergodic if and
only if there exists **no** decomposition

`(1.6.6)  P = β₁P₁ + β₂P₂,  β₁ + β₂ = 1, β₁ > 0, β₂ > 0`,

where `P₁` and `P₂` are, for all `t ∈ ℝ`, `θ_t`-invariant probabilities on `Ω`, with `P₁ ≠ P₂`.

The continuous-time counterpart of Theorem 1.6.3, quoted from the same source (Cornfeld, Fomin and
Sinai (1981)).

The difference from the discrete case is in the quantifier, and it is not cosmetic: `P₁` and `P₂`
must be invariant under **every** `θ_t`, not under one map. A probability invariant under a single
`θ_{t₀}` need not be invariant under the flow. -/
theorem extremal_flow (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Flow Ω) (hinv : θ.Invariant P) :
    IsErgodicFlow θ P ↔ ¬ HasFlowInvariantDecomposition θ P := by sorry

end PalmQueueing.Ergodic

