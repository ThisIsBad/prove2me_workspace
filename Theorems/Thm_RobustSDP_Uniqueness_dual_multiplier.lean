import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix

namespace RobustSDP.Uniqueness

/-- Appendix A, p. 49: under `c ≠ 0`, H1, H2 and H3(a), at every optimal `(x, τ)` of (15) there is a
dual matrix `Z ⪰ 0`, `Z ≠ 0` (the multiplier of `G(y) ⪰ 0` in (16), with `μ = 0`) satisfying
complementarity `Tr Z G(y) = 0`, stationarity in `x`
(`Tr Z ∂G/∂xᵢ = cᵢ`, `∂G/∂xᵢ = Fᵢ − (1/τ)(R(x)ᵀRᵢ + RᵢᵀR(x))`), and, from stationarity in `τ`,
`τ² Tr LLᵀZ = Tr R(x)ᵀR(x)Z`. -/
theorem dual_multiplier {m n p q : ℕ} (D : SDPData m n p q) (c : Fin m → ℝ) (hc : c ≠ 0)
    (hsym : D.Symmetric) (h1 : D.Slater) (h2 : D.InfCompact c) (h3a : D.H3a)
    (x : Fin m → ℝ) (τ : ℝ) (hopt : D.IsOptimal c (x, τ)) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef ∧ Z ≠ 0 ∧
      (Z * D.G (x, τ)).trace = 0 ∧
      (∀ i : Fin m,
        (Z * (D.Fs i - τ⁻¹ • ((D.R x)ᵀ * D.Rs i + (D.Rs i)ᵀ * D.R x))).trace = c i) ∧
      τ ^ 2 * (D.L * D.Lᵀ * Z).trace = ((D.R x)ᵀ * D.R x * Z).trace := by sorry

end RobustSDP.Uniqueness

