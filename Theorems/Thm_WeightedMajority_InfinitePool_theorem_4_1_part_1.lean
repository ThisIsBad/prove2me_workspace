import Mathlib
import Definitions.Def_WeightedMajority_InfinitePool_IsWMI2Run

namespace WeightedMajority.InfinitePool

/-- Theorem 4.1, part 1 (Littlestone–Warmuth 1994, p. 226): at the beginning of any trial the
size of the active pool of WMI₂ is the minimum `l` with `Ŵ(l + 1) ≤ slack m`, where `m` is the
number of mistakes made in prior trials. -/
theorem theorem_4_1_part_1
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (W What : ℕ+ → ℝ) (hW_pos : ∀ i, 0 < W i) (hW_sum : Summable W)
    (hWhat_tail : ∀ i, (∑' j : ℕ+, if i ≤ j then W j else 0) ≤ What i)
    (hWhat_lim : Filter.Tendsto What Filter.atTop (nhds 0))
    {T : ℕ} (x : Fin T → ℕ+ → Bool) (label : Fin T → Bool)
    (mi : ℕ+ → ℕ)
    (hmi : ∀ i, (Finset.univ.filter (fun t : Fin T => x t i ≠ label t)).card ≤ mi i)
    (prediction : Fin T → Bool) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ)
    (hrun : IsWMI2Run β W What x label prediction w l) :
    ∀ t : Fin T,
      What (Nat.succPNat (l t.val)) ≤ slack β What (mistakesBefore prediction label t.val) ∧
      ∀ l' < l t.val,
        slack β What (mistakesBefore prediction label t.val) < What (Nat.succPNat l') := by sorry

end WeightedMajority.InfinitePool

