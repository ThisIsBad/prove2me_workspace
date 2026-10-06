import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Rates_Algorithm

open Filter Topology InnerProductSpace

namespace NesterovFB.Rates

theorem fact_4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : NNReal) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * L < 1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P)
    (hrun : IsAccelFBRun Φ P α s x)
    (hα : 3 < α)
    (xstar : H) (hxstar : ∀ y, theta Ψ Φ xstar ≤ theta Ψ Φ y) :
    ∀ K : ℕ, ((∑ k ∈ Finset.Icc 1 K, (k : ℝ) * (‖x (k + 1) - x k‖ ^ 2 / (2 * s)) : ℝ) : EReal)
      ≤ ((α * (3 * α - 5) / (4 * s * (α - 1) * (α - 3)) : ℝ) : EReal) * energy Ψ Φ α s x xstar 1 := by sorry

end NesterovFB.Rates

