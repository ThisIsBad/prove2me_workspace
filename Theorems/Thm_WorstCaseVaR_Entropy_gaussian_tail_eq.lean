import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

/-- p. 554: under the reference Gaussian `P₀ = 𝒩(x̂, Γ)` with `Γ ≻ 0` and `w ≠ 0`,
`φ(γ) := Prob{γ ≤ -xᵀw} = 1 - Φ((γ + wᵀx̂)/√(wᵀΓw))`. -/
theorem gaussian_tail_eq {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) (γ : ℝ) :
    (refGaussian xhat Γ).real (lossSet w γ) = gaussianTail xhat Γ w γ := by sorry

end WorstCaseVaR.Entropy
