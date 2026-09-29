import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Blackwell (1956), §3, proof of THEOREM 3, p. 6, second paragraph: every `T(q₀)` is
approachable in the transpose `M'` with the stationary strategy `fₙ ≡ q₀`. -/
theorem T_approachable_transpose {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ)
    (hq₀ : q₀ ∈ stdSimplex ℝ (Fin s)) :
    G.transpose.ApproachableWith (G.T q₀) (Strategy.const q₀ hq₀) := by sorry

end VectorPayoffs.Convex
