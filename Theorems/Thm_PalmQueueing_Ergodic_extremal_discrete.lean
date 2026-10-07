import Mathlib
import Definitions.Def_PalmQueueing_Ergodic_DiscreteFlow

/-!
# Theorem 1.6.3: the extremal characterization of discrete ergodic flows (§1.6.1, p.48)
-/

namespace PalmQueueing.Ergodic

open MeasureTheory
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 1.6.3 (Extremal properties of ergodic flows)** (p.48). `(P⁰_N, θ)` is ergodic if and
only if there exists **no** decomposition

`(1.6.4)  P⁰_N = α₁Q₁ + α₂Q₂,  α₁ + α₂ = 1, α₁ > 0, α₂ > 0`,

where `Q₁` and `Q₂` are `θ`-invariant probabilities with `Q₁ ≠ Q₂`.

Ergodicity is an **extremality** property: the ergodic invariant measures are exactly the extreme
points of the convex set of invariant probabilities. That is what makes "ergodic" the right notion
of indecomposability, and it is why the ergodic decomposition theorem looks the way it does.

The book quotes this result rather than proving it: "For a proof, see Billingsley (1965),
pp. 38-39."

The statement is an equivalence, and its right-hand side is a **negation** — the absence of a
decomposition. Stating only that an ergodic flow admits no decomposition would drop the half that
is used in practice.

`hbij` is the book's definition of a discrete flow (p.46). -/
theorem extremal_discrete (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (θ : Ω → Ω) (hθ : Measurable θ) (hbij : Function.Bijective θ) (hinv : Measure.map θ P0 = P0) :
    Ergodic θ P0 ↔ ¬ HasInvariantDecomposition θ P0 := by sorry

end PalmQueueing.Ergodic

