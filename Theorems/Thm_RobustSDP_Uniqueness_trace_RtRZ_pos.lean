import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix

namespace RobustSDP.Uniqueness

/-- Appendix A, p. 49: by H3(b), `Tr LLᵀZ = 0` and `Tr R(x)ᵀR(x)Z = 0` cannot both hold for
`Z ⪰ 0`, `Z ≠ 0`; with `τ ≠ 0` and `τ² Tr LLᵀZ = Tr R(x)ᵀR(x)Z` this yields
`Tr R(x)ᵀR(x)Z > 0`. -/
theorem trace_RtRZ_pos {m n p q : ℕ} (D : SDPData m n p q) (h3b : D.H3b)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosSemidef) (hZ0 : Z ≠ 0)
    (x : Fin m → ℝ) (τ : ℝ) (hτ : τ ≠ 0) :
    ¬ ((D.L * D.Lᵀ * Z).trace = 0 ∧ ((D.R x)ᵀ * D.R x * Z).trace = 0) ∧
      (τ ^ 2 * (D.L * D.Lᵀ * Z).trace = ((D.R x)ᵀ * D.R x * Z).trace →
        0 < ((D.R x)ᵀ * D.R x * Z).trace) := by sorry

end RobustSDP.Uniqueness
