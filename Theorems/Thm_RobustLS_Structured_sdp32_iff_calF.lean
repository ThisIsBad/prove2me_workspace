import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

/-- **§4.2, the Schur-complement step** — El Ghaoui & Lebret (1997), §4.2, p. 1045 (PDF p. 11):
"Using Theorem 4.1, the expression of F, g, h given in (27), and Schur complements, we obtain the
following result." For all `λ, τ, x`, the matrix of the SDP (32),
`[λ − τ, 0, (A₀x − b₀)ᵀ; 0, τI, M(x)ᵀ; A₀x − b₀, M(x), I]`, is positive semidefinite if and only if
`𝓕(λ, τ) = [λ − τ − h, −gᵀ; −g, τI − F]` of (29), built from `x` via (27), is. -/
theorem sdp32_iff_calF {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (lam τ : ℝ) (x : Fin m → ℝ) :
    SDP32Feasible A0 A b0 b lam τ x ↔ (calF A0 A b0 b x lam τ).PosSemidef := by sorry

end RobustLS.Structured
