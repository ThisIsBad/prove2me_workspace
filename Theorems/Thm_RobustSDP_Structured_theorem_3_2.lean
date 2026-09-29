import Mathlib
import Definitions.Def_RobustSDP_Structured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Structured

/-- Theorem 3.2, p. 37, read as an inner approximation of the robust feasible set, with the LMI
**corrected** as in Lemma 3.2. Let `F(x) = F₀ + ∑ xᵢFᵢ` (`Fᵢ` symmetric) and
`R(x) = R₀ + ∑ xᵢRᵢ` be affine, `L`, `D` fixed, `𝒟` a linear subspace of `ℝ^{p×q}` and `ρ > 0`.
If `x` admits `(S, T, G) ∈ 𝓑` with `S ≻ 0`, `T ≻ 0` and
`[[F(x) − LSLᵀ, R(x)ᵀ − LSDᵀ + LG], [R(x) − DSLᵀ + GᵀLᵀ, ρ⁻²T − DSDᵀ + DG + GᵀDᵀ]] ≻ 0`,
then `x` lies in the robust feasible set `𝒳_ρ` (2), and in fact `F(x, Δ) ≻ 0` for every
`Δ ∈ 𝒟` with `‖Δ‖ ≤ ρ`. -/
theorem theorem_3_2 {m n p q : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (Rs : Fin (m + 1) → Matrix (Fin q) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) (D : Matrix (Fin q) (Fin p) ℝ)
    (𝒟 : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ)) (ρ : ℝ) (hρ : 0 < ρ) (x : Fin m → ℝ)
    (hx : ∃ (S : Matrix (Fin p) (Fin p) ℝ) (T : Matrix (Fin q) (Fin q) ℝ)
        (G : Matrix (Fin p) (Fin q) ℝ), (S, T, G) ∈ scalingSet 𝒟 ∧ S.PosDef ∧ T.PosDef ∧
          (structuredLMI (affineMap Fs x) (affineMap Rs x) L D S T G ρ).PosDef) :
    x ∈ robustFeasibleSet Fs Rs L D 𝒟 ρ ∧
      ∀ Δ ∈ 𝒟, ‖Δ‖ ≤ ρ → (lfr (affineMap Fs x) (affineMap Rs x) L D Δ).PosDef := by sorry

end RobustSDP.Structured

