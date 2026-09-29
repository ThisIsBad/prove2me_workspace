import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

/-- p. 554: the worst-case probability `sup_{P : KL(P, P₀) ≤ d} P{γ ≤ -xᵀw}` equals the
infimum over `λ > 0` of `λd + λ log((e^{1/λ} - 1)φ(γ) + 1)`, where `φ(γ) = P₀{γ ≤ -xᵀw}`. -/
theorem worst_case_probability_dual {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) (d : ℝ) (hd : 0 ≤ d) (γ : ℝ) :
    ∃ θ : ℝ,
      IsLUB {p | ∃ P ∈ klBall xhat Γ d, P.real (lossSet w γ) = p} θ ∧
      IsGLB (dualValue d ((refGaussian xhat Γ).real (lossSet w γ)) '' Set.Ioi 0) θ := by sorry

end WorstCaseVaR.Entropy
