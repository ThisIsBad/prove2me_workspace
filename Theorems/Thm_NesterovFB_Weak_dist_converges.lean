import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Weak_Algorithm
open Filter Topology NNReal

namespace NesterovFB.Weak

theorem dist_converges
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : ℝ≥0) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P)
    (hα : 3 < α)
    (hrun : NesterovFB.Rates.IsAccelFBRun Φ P α s x)
    (xstar : H) (hxstar : ∀ y, NesterovFB.Rates.theta Ψ Φ xstar ≤ NesterovFB.Rates.theta Ψ Φ y) :
    ∃ l : ℝ, Tendsto (fun k => ‖x k - xstar‖) atTop (𝓝 l) := by sorry

end NesterovFB.Weak

