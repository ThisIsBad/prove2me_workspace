import Mathlib
import Definitions.Def_TalagrandConc_BinPacking_Basic

namespace TalagrandConc.BinPacking

/-- Talagrand (1995), p. 151, Lemma 6.1: `B_N(x₁, …, x_N) ≤ 2 ∑_{i ≤ N} x_i + 1`. -/
theorem lemma_6_1 {N : ℕ} (x : Fin N → unitInterval) :
    (binNumber x : ℝ) ≤ 2 * ∑ i, (x i : ℝ) + 1 := by sorry

end TalagrandConc.BinPacking

