import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Rates_Algorithm

open Filter Topology InnerProductSpace

namespace NesterovFB.Rates

theorem theorem_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : NNReal) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * L < 1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P)
    (hrun : IsAccelFBRun Φ P α s x)
    (hα : 3 < α)
    (hS : ∃ xstar : H, ∀ y, theta Ψ Φ xstar ≤ theta Ψ Φ y) :
    Tendsto (fun k : ℕ => (((k : ℝ) ^ 2 : ℝ) : EReal) * (theta Ψ Φ (x k) - ⨅ y, theta Ψ Φ y))
        atTop (𝓝 0) ∧
      Tendsto (fun k : ℕ => (k : ℝ) * ‖x (k + 1) - x k‖) atTop (𝓝 0) := by sorry

end NesterovFB.Rates

