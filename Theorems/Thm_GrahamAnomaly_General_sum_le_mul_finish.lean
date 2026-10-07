import Mathlib
import Definitions.Def_GrahamAnomaly_General_Model

namespace GrahamAnomaly.General

/-- The work-volume step used in display (5): `n` processors provide at most
`n * ω` units of processing before the finish. -/
theorem sum_le_mul_finish {r n : ℕ}
    (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (prec : Fin r → Fin r → Prop) (G : Schedule n μ prec) :
    ∑ j, μ j ≤ (n : ℝ) * G.finish := by sorry

end GrahamAnomaly.General

