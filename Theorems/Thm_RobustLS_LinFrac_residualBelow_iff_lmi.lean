import Mathlib
import Definitions.Def_RobustLS_LinFrac_Core

open Matrix

namespace RobustLS.LinFrac

/-- El Ghaoui & Lebret (1997), §5.4, p. 1047 (PDF p. 13): "Let λ ∈ ℝ. The inequality
λ > r_𝒟(A, b, x) holds if and only if, for every Δ ∈ 𝒟, ‖Δ‖ ≤ 1, we have det(I − DΔ) ≠ 0 and
[[λI, Ax − b], [(Ax − b)ᵀ, λ]] + [L; 0]Δ(I − DΔ)⁻¹[0  R_Ax − R_b]
+ [0; (R_Ax − R_b)ᵀ](I − DΔ)⁻ᵀΔᵀ[Lᵀ  0] > 0."
Here `ResidualBelow` encodes `λ > r_𝒟(A, b, x)` with `ρ = 1`, including the value `∞` of (35). -/
theorem residualBelow_iff_lmi {n m N : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ))
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (L : Matrix (Fin n) (Fin N) ℝ)
    (RA : Matrix (Fin N) (Fin m) ℝ) (Rb : Fin N → ℝ) (D : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin m → ℝ) (lam : ℝ) :
    ResidualBelow 𝒟 A b L RA Rb D x lam ↔
      ∀ Δ ∈ 𝒟, specNorm Δ ≤ 1 →
        (1 - D * Δ).det ≠ 0 ∧ (residualLMI A b L RA Rb D x lam Δ).PosDef := by sorry

end RobustLS.LinFrac
