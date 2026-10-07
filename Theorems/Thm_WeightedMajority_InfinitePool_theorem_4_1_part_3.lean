import Mathlib
import Definitions.Def_WeightedMajority_InfinitePool_IsWMI2Run

namespace WeightedMajority.InfinitePool

/-- Theorem 4.1, part 3 (Littlestone–Warmuth 1994, p. 227). If `0 < β < 1`, the total number
`m` of mistakes of WMI₂ is at most `(log(Ŵ(1)/W(i)) + m_i log(1/β) + log 2) / log(1/u)` for every
`i` (equivalently, at most the infimum over `i ≥ 1`). If `β = 0` and `m_i = 0` for some `i`, then
`m ≤ 1 + log₂(Ŵ(1)/W(i))`. -/
theorem theorem_4_1_part_3
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (W What : ℕ+ → ℝ) (hW_pos : ∀ i, 0 < W i) (hW_sum : Summable W)
    (hWhat_tail : ∀ i, (∑' j : ℕ+, if i ≤ j then W j else 0) ≤ What i)
    (hWhat_lim : Filter.Tendsto What Filter.atTop (nhds 0))
    {T : ℕ} (x : Fin T → ℕ+ → Bool) (label : Fin T → Bool)
    (mi : ℕ+ → ℕ)
    (hmi : ∀ i, (Finset.univ.filter (fun t : Fin T => x t i ≠ label t)).card ≤ mi i)
    (prediction : Fin T → Bool) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ)
    (hrun : IsWMI2Run β W What x label prediction w l) :
    (0 < β → ∀ i : ℕ+,
      (mistakesBefore prediction label T : ℝ) ≤
        (Real.log (What 1 / W i) + (mi i : ℝ) * Real.log (1 / β) + Real.log 2) /
          Real.log (1 / u β)) ∧
    (β = 0 → ∀ i : ℕ+, mi i = 0 →
      (mistakesBefore prediction label T : ℝ) ≤ 1 + Real.logb 2 (What 1 / W i)) := by sorry

end WeightedMajority.InfinitePool

