import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic
import Definitions.Def_TalagrandConc_Subsequences_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.Subsequences

/-- Talagrand (1995), Eq. (7.2.3), p. 155. With `Ω = [0,1]`, `x ∈ Ω^{N+N'}`,
`L(x) = L_{N,N'}(x_1, …, x_N; x_{N+1}, …, x_{N+N'})` and `A(a) = {x ; L(x) ≤ a}`, for `a > 0`:
`a ≥ L(x) − 2√2 f_c(A(a), x) √(L(x))`, written as
`L(x) ≤ a + 2√2 f_c(A(a), x) √(L(x))` in `ℝ≥0∞`. -/
theorem eq_7_2_3 {N N' : ℕ} (a : ℝ) (ha : 0 < a) (x : Fin (N + N') → unitInterval) :
    ((lcsJoint x : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal a + ENNReal.ofReal (2 * Real.sqrt 2) * TalagrandConc.ConvexHull.fc (levelSet lcsJoint a) x *
        ENNReal.ofReal (Real.sqrt (lcsJoint x)) := by sorry

end TalagrandConc.Subsequences

