import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Theorem 1.5.1: conditioning at a point (§1.5.2, p.45)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 1.5.1** (§1.5.2, p.45), the local aspect of Palm probability:

`(1.5.3)  lim_{t → 0} sup_{A ∈ F} | P⁰_N(A) - P(θ_{T₁} ∈ A | T₁ ≤ t) | = 0`.

The Palm probability is the limit of conditioning on there being a point in a shrinking window to
the right of the origin — the statement that makes "what an arriving customer sees" precise. The
supremum over `A ∈ F` is inside the limit and is not decorative: the convergence is **uniform over
all measurable events**, which is what the proof's Dobrushin estimate (§1.5.1) buys and what a
pointwise limit would not give. The `ε`-`δ` form below says exactly that: one `δ` serves every `A`
at once. -/
theorem palm_local_limit (S : PalmSetting Ω)
    (hshift : Measurable fun ω => S.θ (S.N.T 1 ω) ω) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ A : Set Ω, MeasurableSet A →
        |(S.P0 A).toReal
            - (S.P ({ω | S.θ (S.N.T 1 ω) ω ∈ A} ∩ {ω | S.N.T 1 ω ≤ t})).toReal
                / (S.P {ω | S.N.T 1 ω ≤ t}).toReal| ≤ ε := by sorry

end PalmQueueing.Palm

