import Mathlib
import Definitions.Def_BurnInBatch_ListSched_Model

namespace BurnInBatch.ListSched

/-- Proposition 4, p. 773: the relative maximum-lateness error of BLS.
The hypothesis `hd` (nonnegative due dates) is not printed in the proposition; the
proof's last step `d_max - d^k ≤ d_max` uses it, and without it the statement fails
(one job, `p = 4`, `d = -3`, `B = 1`, `m = 2`). -/
theorem proposition_4 {n : ℕ} (p d : Fin n → ℝ) (B m : ℕ)
    (l : List (Fin n)) (hn : 0 < n) (hB : 0 < B) (hm : 0 < m)
    (hp : ∀ j, 0 < p j) (hd : ∀ j, 0 ≤ d j)
    (hl : ListsJobs Finset.univ l) :
    (blsLateness p d B m hm l Finset.univ - LStar p d B m Finset.univ) /
        (LStar p d B m Finset.univ + maxDue d hn) ≤
      ((B : ℝ) - 1 / (m : ℝ)) +
        maxDue d hn / (LStar p d B m Finset.univ + maxDue d hn) := by sorry

end BurnInBatch.ListSched

