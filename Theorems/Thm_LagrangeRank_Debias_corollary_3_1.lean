import Mathlib
import Definitions.Def_LagrangeRank_Debias_Setting

namespace LagrangeRank.Debias
open Matrix
theorem corollary_3_1 (c1 c2 c3 L2 : ℝ) (hc3 : 0 < c3) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (d : ℕ) (OmHat OmStar : Matrix (Fin d) (Fin d) ℝ) (gHat gStar : Fin d → ℝ)
        (ρ1 ρ4 : ℝ),
        0 ≤ ρ1 → 0 ≤ ρ4 → ρ1 + ρ4 ≤ δ →
        l1Norm gStar ≤ c1 → l1Norm (gHat - gStar) ≤ L2 * ρ1 →
        rowSumNorm OmStar ≤ c2 → c3 ≤ gStar ⬝ᵥ (OmStar *ᵥ gStar) →
        rowSumNorm (OmHat - OmStar) ≤ ρ4 →
        |(thetaBlock OmHat gHat - thetaBlock OmStar gStar).toBlocks₂₂ () ()|
            ≤ C * (ρ1 + ρ4) ∧
        ‖fun k => (thetaBlock OmHat gHat - thetaBlock OmStar gStar).toBlocks₁₂ k ()‖
            ≤ C * (ρ1 + ρ4) ∧
        rowSumNorm (thetaBlock OmHat gHat - thetaBlock OmStar gStar).toBlocks₁₁
            ≤ C * (ρ1 + ρ4) := by sorry
end LagrangeRank.Debias

