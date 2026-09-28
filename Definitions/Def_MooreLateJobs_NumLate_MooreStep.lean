import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet

namespace MooreLateJobs.NumLate

/-- One pass of Steps 2–3 of Moore's algorithm (p. 103), on states `(cur, rej)` = (current
sequence, list of rejected jobs in order of rejection).

`MooreStep t D (cur, rej) (cur', rej')` holds iff, with `q` the (0-based) position of the first
late job `J_{i_q}` of the current sequence (Step 2), and `pre'` a re-ordering of the prefix
`J_{i_1} ⋯ J_{i_q}` (the first `q + 1` jobs, the late job included) according to the due-date rule
(Step 3, ties broken arbitrarily), either
1) every job of `pre'` is early in `pre'`, and the new current sequence is `pre'` followed by the
   rest `J_{i_{q+1}} ⋯ J_{i_n}` of the current sequence, nothing rejected; or
2) some job of `pre'` is late in `pre'`, the job `J_{i_q}` is rejected (appended to `rej`) and
   removed from `pre'`, and the new current sequence is the rest of `pre'` followed by
   `J_{i_{q+1}} ⋯ J_{i_n}`. -/
def MooreStep {ι : Type*} [DecidableEq ι] (t D : ι → ℝ) (s s' : List ι × List ι) : Prop :=
  ∃ (q : ℕ) (hq : q < s.1.length),
    D (s.1[q]'hq) < Shared.completionAt t s.1 q ∧
    (∀ (k : ℕ) (hk : k < q), Shared.completionAt t s.1 k ≤ D (s.1[k]'(lt_trans hk hq))) ∧
    ∃ pre' : List ι, pre'.Perm (s.1.take (q + 1)) ∧ pre'.Pairwise (fun a b => D a ≤ D b) ∧
      ((lateSet t D pre' = ∅ ∧ s' = (pre' ++ s.1.drop (q + 1), s.2)) ∨
       ((lateSet t D pre').Nonempty ∧
          s' = (pre'.erase (s.1[q]'hq) ++ s.1.drop (q + 1), s.2 ++ [s.1[q]'hq])))

end MooreLateJobs.NumLate
