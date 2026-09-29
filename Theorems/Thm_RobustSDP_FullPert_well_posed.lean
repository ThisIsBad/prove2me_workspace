import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.FullPert

/-- §3.1, p. 36 (first paragraph): for `ρ > 0`, `F(x, Δ)` is well defined, i.e.
`det (I − DΔ) ≠ 0`, for every `Δ ∈ ℝ^{p×q}` with `‖Δ‖ ≤ ρ` if and only if `‖D‖ < ρ⁻¹`
(spectral norms). -/
theorem well_posed {p q : ℕ} (D : Matrix (Fin q) (Fin p) ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ Δ : Matrix (Fin p) (Fin q) ℝ, ‖Δ‖ ≤ ρ → (1 - D * Δ).det ≠ 0) ↔ ‖D‖ < ρ⁻¹ := by sorry

end RobustSDP.FullPert

