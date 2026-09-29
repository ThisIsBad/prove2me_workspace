import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.FullPert

/-- Lemma 3.1, p. 36, with the hypothesis `L ≠ 0` added (the printed statement fails for
`L = 0`: take `n = p = q = 1`, `F = 0`, `L = 0`, `D = 0`, `R = 1`; then (8) holds but (9) is
`[[0, 1], [1, τ]] ⪰ 0`, which no `τ` satisfies) and `0 < q` made explicit ("matrices of
appropriate size"). For `F = Fᵀ`: `det (I − DΔ) ≠ 0` and
`F + LΔ(I − DΔ)⁻¹R + Rᵀ(I − DΔ)⁻ᵀΔᵀLᵀ ⪰ 0` for every `Δ` with `‖Δ‖ ≤ 1` (8) iff `‖D‖ < 1` and
some scalar `τ` makes the block matrix (9) positive semidefinite. -/
theorem lemma_3_1 {n p q : ℕ} (hq : 0 < q) (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (L : Matrix (Fin n) (Fin p) ℝ) (R : Matrix (Fin q) (Fin n) ℝ) (D : Matrix (Fin q) (Fin p) ℝ)
    (hL : L ≠ 0) :
    (∀ Δ : Matrix (Fin p) (Fin q) ℝ, ‖Δ‖ ≤ 1 →
        (1 - D * Δ).det ≠ 0 ∧
          (F + L * Δ * (1 - D * Δ)⁻¹ * R + Rᵀ * ((1 - D * Δ)⁻¹)ᵀ * Δᵀ * Lᵀ).PosSemidef) ↔
      (‖D‖ < 1 ∧ ∃ τ : ℝ,
        (fromBlocks (F - τ • (L * Lᵀ)) (Rᵀ - τ • (L * Dᵀ)) (R - τ • (D * Lᵀ))
          (τ • (1 - D * Dᵀ))).PosSemidef) := by sorry

end RobustSDP.FullPert

