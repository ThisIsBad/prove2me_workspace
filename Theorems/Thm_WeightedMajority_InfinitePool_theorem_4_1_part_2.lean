import Mathlib
import Definitions.Def_WeightedMajority_InfinitePool_IsWMI2Run

namespace WeightedMajority.InfinitePool

/-- Theorem 4.1, part 2 (Littlestone–Warmuth 1994, p. 227): after any initial sequence of
trials in which `m` mistakes have been made, `∑ ω_i ≤ (2 - 1/(m+1)) u^m Ŵ(1)`, where `ω_i` is
the current weight of an active member and `W(i)` for an inactive one. The family `ω` is also
asserted to be summable. -/
theorem theorem_4_1_part_2
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (W What : ℕ+ → ℝ) (hW_pos : ∀ i, 0 < W i) (hW_sum : Summable W)
    (hWhat_tail : ∀ i, (∑' j : ℕ+, if i ≤ j then W j else 0) ≤ What i)
    (hWhat_lim : Filter.Tendsto What Filter.atTop (nhds 0))
    {T : ℕ} (x : Fin T → ℕ+ → Bool) (label : Fin T → Bool)
    (mi : ℕ+ → ℕ)
    (hmi : ∀ i, (Finset.univ.filter (fun t : Fin T => x t i ≠ label t)).card ≤ mi i)
    (prediction : Fin T → Bool) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ)
    (hrun : IsWMI2Run β W What x label prediction w l) :
    ∀ t ≤ T,
      Summable (omega W w l t) ∧
      ∑' i, omega W w l t i ≤
        (2 - 1 / ((mistakesBefore prediction label t : ℝ) + 1)) *
          u β ^ mistakesBefore prediction label t * What 1 := by sorry

end WeightedMajority.InfinitePool

