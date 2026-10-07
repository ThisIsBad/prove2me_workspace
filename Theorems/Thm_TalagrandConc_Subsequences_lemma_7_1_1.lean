import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic
import Definitions.Def_TalagrandConc_Subsequences_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.Subsequences

/-- Talagrand (1995), Lemma 7.1.1, p. 153. For `a > 0` and every `x ∈ [0,1]^N`,
(7.1.1) `a ≥ L_N(x) − f_c(A(a), x) √(L_N(x))`, written as `L_N(x) ≤ a + f_c(A(a), x) √(L_N(x))`
in `ℝ≥0∞` (where `f_c = +∞` when `A(a) = ∅`), and
(7.1.2) `L_N(x) ≥ a + v ⇒ f_c(A(a), x) ≥ v / √(a + v)` for every real `v`
(for `v < 0` the bound is trivial). -/
theorem lemma_7_1_1 {N : ℕ} (a : ℝ) (ha : 0 < a) (x : Fin N → unitInterval) :
    ((lis x : ℕ) : ℝ≥0∞) ≤
        ENNReal.ofReal a + TalagrandConc.ConvexHull.fc (levelSet lis a) x * ENNReal.ofReal (Real.sqrt (lis x)) ∧
      ∀ v : ℝ, a + v ≤ (lis x : ℝ) →
        ENNReal.ofReal (v / Real.sqrt (a + v)) ≤ TalagrandConc.ConvexHull.fc (levelSet lis a) x := by sorry

end TalagrandConc.Subsequences

