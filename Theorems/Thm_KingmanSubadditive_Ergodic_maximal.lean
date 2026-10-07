import Mathlib
import Definitions.Def_KingmanSubadditive_Ergodic_Process

namespace KingmanSubadditive.Ergodic

open MeasureTheory

/-- Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973),
p. 885, (1.2.5), quoted from [8]. The printed conditional-expectation
notation is read as the integral over the event where some `x₀ₜ ≥ 0`;
it has the same sign when the event has positive probability and also
makes sense when its probability is zero. -/
theorem maximal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hx : IsSubadditiveProcess P x) :
    0 ≤ ∫ ω in {ω | ∃ t : ℕ, 1 ≤ t ∧ 0 ≤ x 0 t ω}, x 0 1 ω ∂P := by sorry

end KingmanSubadditive.Ergodic

