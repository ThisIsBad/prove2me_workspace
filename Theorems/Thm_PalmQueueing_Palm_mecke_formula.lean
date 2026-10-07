import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Eq. (1.2.17): Mecke's formula (p.17)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Mecke's formula**, Eq. (1.2.17) (p.17), the central identity of Palm calculus, which the
book also calls the generalized Campbell formula:

`λ ∫∫_{Ω × ℝ} v(ω, t) P⁰_N(dω) dt = ∫∫_{Ω × ℝ} v(θ_t ω, t) P(dω) N(ω, dt)`

for every non-negative measurable `v : (Ω × ℝ, F ⊗ B) → (ℝ, B)`. The page derives it for
`v(ω, t) = 1_A(ω) 1_C(t)` straight from the defining formula (1.2.1) of `P⁰_N` and then extends it
to all such `v` by a monotone class argument; both sides are stated here in `ℝ≥0∞`, which is where
"non-negative measurable, no integrability hypothesis" lives.

It has content precisely because `P⁰_N` is defined by counting (1.2.1) and not as "a measure
satisfying this formula". -/
theorem mecke_formula (S : PalmSetting Ω) (v : Ω → ℝ → ENNReal)
    (hv : Measurable (Function.uncurry v)) :
    ENNReal.ofReal S.lam * ∫⁻ ω, ∫⁻ t, v ω t ∂(volume : Measure ℝ) ∂S.P0
      = ∫⁻ ω, ∫⁻ t, v (S.θ t ω) t ∂(S.N.count ω) ∂S.P := by sorry

end PalmQueueing.Palm

