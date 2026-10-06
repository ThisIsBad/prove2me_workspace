import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Rates_Algorithm

open Filter Topology InnerProductSpace

namespace NesterovFB.Rates

theorem eq9_prox_grad_inequality {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : NNReal) (s : ℝ) (P : H → H)
    (hΨ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL' : s * L ≤ 1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P) :
    ∀ x y : H, theta Ψ Φ (y - s • gradMap Φ P s y) ≤ theta Ψ Φ x
      + ((⟪gradMap Φ P s y, y - x⟫_ℝ - s / 2 * ‖gradMap Φ P s y‖ ^ 2 : ℝ) : EReal) := by sorry

end NesterovFB.Rates

