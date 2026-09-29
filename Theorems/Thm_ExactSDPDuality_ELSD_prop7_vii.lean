import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

/-- Proposition 7(vii) (Ramana 1997, p. 139): if `U − WWᵀ ⪰ 0`, then `W = UH` for some
(not necessarily symmetric) real matrix `H`. -/
theorem prop7_vii {n : ℕ} (U W : Matrix (Fin n) (Fin n) ℝ)
    (h : (U - W * Wᵀ).PosSemidef) :
    ∃ H : Matrix (Fin n) (Fin n) ℝ, W = U * H := by sorry

end ExactSDPDuality.ELSD
