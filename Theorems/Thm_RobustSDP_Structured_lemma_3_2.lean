import Mathlib
import Definitions.Def_RobustSDP_Structured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Structured

/-- Lemma 3.2, p. 37, with the matrix (13) and the `G`-part of (11) **corrected** (as printed,
(13) contains the undefined products `LG`, `DSL`, `DG`). Let `F = Fᵀ` (`n × n`), `L` (`n × p`),
`R` (`q × n`), `D` (`q × p`), and let `𝒟` be a linear subspace of `ℝ^{p×q}`. If some triple
`(S, T, G) ∈ 𝓑` (`scalingSet 𝒟`) has `S ≻ 0`, `T ≻ 0` and
`[[F − LSLᵀ, Rᵀ − LSDᵀ + LG], [R − DSLᵀ + GᵀLᵀ, T − DSDᵀ + DG + GᵀDᵀ]] ≻ 0`,
then for every `Δ ∈ 𝒟` with `‖Δ‖ ≤ 1` (spectral norm): `det (I − DΔ) ≠ 0` and
`F + LΔ(I − DΔ)⁻¹R + Rᵀ(I − DΔ)⁻ᵀΔᵀLᵀ ≻ 0` (12). -/
theorem lemma_3_2 {n p q : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (L : Matrix (Fin n) (Fin p) ℝ) (R : Matrix (Fin q) (Fin n) ℝ) (D : Matrix (Fin q) (Fin p) ℝ)
    (𝒟 : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ))
    (S : Matrix (Fin p) (Fin p) ℝ) (T : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin p) (Fin q) ℝ)
    (hB : (S, T, G) ∈ scalingSet 𝒟) (hS : S.PosDef) (hT : T.PosDef)
    (hLMI : (fromBlocks (F - L * S * Lᵀ) (Rᵀ - L * S * Dᵀ + L * G) (R - D * S * Lᵀ + Gᵀ * Lᵀ)
      (T - D * S * Dᵀ + D * G + Gᵀ * Dᵀ)).PosDef) :
    ∀ Δ ∈ 𝒟, ‖Δ‖ ≤ 1 →
      (1 - D * Δ).det ≠ 0 ∧
        (F + L * Δ * (1 - D * Δ)⁻¹ * R + Rᵀ * ((1 - D * Δ)⁻¹)ᵀ * Δᵀ * Lᵀ).PosDef := by sorry

end RobustSDP.Structured

