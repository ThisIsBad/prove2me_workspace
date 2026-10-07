import Mathlib
import Definitions.Def_TalagrandConc_BinPacking_Basic

namespace TalagrandConc.BinPacking

open scoped ENNReal

/-- Talagrand (1995), p. 151, Lemma 6.2, Eq. (6.2): for `a > 0` and all `x ∈ Ω^N`,
`B_N(x) ≤ a + 2 ‖x‖₂ f_c(A(a), x) + 1`. Computed in `ℝ≥0∞` (`f_c = ⊤` when `A(a) = ∅`). -/
theorem lemma_6_2 {N : ℕ} (a : ℝ) (ha : 0 < a) (x : Fin N → unitInterval) :
    (binNumber x : ℝ≥0∞) ≤
      ENNReal.ofReal a + 2 * ENNReal.ofReal (l2Norm x) * convexDist (levelSet N a) x + 1 := by sorry

end TalagrandConc.BinPacking

