import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix

namespace RobustSDP.Uniqueness

/-- Appendix A, pp. 49–50: if `τ > 0`, `Z ⪰ 0`, `Tr R(x)ᵀR(x)Z > 0` and H3(a) holds, then the Hessian
at `y = (x, τ)` of the Lagrangian `ℒ(y) = cᵀx − Tr Z G(y)` of (16) (dual variable `Y = diag(Z, 0)`)
is positive definite. -/
theorem hessian_lagrangian_posDef {m n p q : ℕ} (D : SDPData m n p q) (h3a : D.H3a)
    (c : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosSemidef)
    (x : Fin m → ℝ) (τ : ℝ) (hτ : 0 < τ) (htr : 0 < ((D.R x)ᵀ * D.R x * Z).trace) :
    ∀ h : (Fin m → ℝ) × ℝ, h ≠ 0 →
      0 < iteratedFDeriv ℝ 2
        (fun y : (Fin m → ℝ) × ℝ => c ⬝ᵥ y.1 - (Z * D.G y).trace) (x, τ) ![h, h] := by sorry

end RobustSDP.Uniqueness

