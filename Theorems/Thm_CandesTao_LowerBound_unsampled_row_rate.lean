import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace CandesTao.LowerBound

theorem unsampled_row_rate (n : ℕ) (π δ : ℝ)
    (hn : 1 ≤ n) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (h : (1 - π) ^ n ≥ 1 - δ) :
    π ≤ 2 * δ / n := by sorry

end CandesTao.LowerBound
