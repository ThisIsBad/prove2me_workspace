import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoTimes_Theorem7Instance

open MatousekLP.Scheduling

namespace UnrelatedSched.TwoTimes

/-- Theorem 7 (Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), p. 8; proof pp. 8–9), in the
form its proof establishes, for relatively prime `0 < p < q` (the paper's "without loss of
generality"): the scheduling instance `twoTimes p q n S` built from a family `S` of `m` `q`-subsets
of a ground set of `qn` elements has all processing times in `{p, q}`, and it has a schedule with
makespan at most `p * q` if and only if `S` has a matching. "NP-hard" is not formalized, and the
hypothesis `2p ≠ q` of the paper, which the reduction does not use, is dropped. -/
theorem theorem_7 {p q m n : ℕ} (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (S : Fin m → Finset (Fin (q * n))) (hS : ∀ i, (S i).card = q) :
    (∀ i j, twoTimes p q n S i j = p ∨ twoTimes p q n S i j = q) ∧
      ((∃ σ : Fin (q * n + p * (m - n)) → Fin m,
          makespan (fun i j => (twoTimes p q n S i j : ℝ)) σ ≤ (p * q : ℝ)) ↔
        ∃ F' : Finset (Fin m), IsQMatching S F') := by sorry

end UnrelatedSched.TwoTimes

