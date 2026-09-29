import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

/-- **Eq. (28)** — El Ghaoui & Lebret (1997), §4.1, p. 1044 (PDF p. 10). With `ρ = 1` and
`F, g, h` as in (27),
`r_S(A, b, x)² = max_{δᵀδ ≤ 1} [1; δ]ᵀ [h gᵀ; g F] [1; δ]`.
The maximum is encoded as "an upper bound on the whole ball, attained at some `δ` of the ball". -/
theorem worst_case_residual_sq_quadratic {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) :
    (∀ δ : Fin p → ℝ, δ ⬝ᵥ δ ≤ 1 →
        oneStack δ ⬝ᵥ (hgFBlock A0 A b0 b x *ᵥ oneStack δ) ≤ rS A0 A b0 b 1 x ^ 2) ∧
      ∃ δ : Fin p → ℝ, δ ⬝ᵥ δ ≤ 1 ∧
        oneStack δ ⬝ᵥ (hgFBlock A0 A b0 b x *ᵥ oneStack δ) = rS A0 A b0 b 1 x ^ 2 := by sorry

end RobustLS.Structured
