import Mathlib
import Definitions.Def_BurnInBatch_TardyJobs_Model

namespace BurnInBatch.TardyJobs

/-- Algorithm DP3, §4, pp. 770–771. `dp3 B p r d i j` is the minimum
completion time of exactly `i` on-time jobs among the first `j` jobs;
`⊤` means no such partial schedule exists. -/
def dp3 {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ) (i j : ℕ) : WithTop ℕ :=
  if hi0 : i = 0 then 0
  else if hgt : i > j then ⊤
  else if hj : j ≤ n then
    have hi : i ≤ j := by omega
    have hjpos : 0 < j := by omega
    let skip := dp3 B p r d i (j - 1)
    let take := (Finset.Icc 1 (min B i)).attach.inf (fun k =>
      let start := max (dp3 B p r d (i - k.val) (j - k.val))
        ((r ⟨j - 1, by omega⟩ : ℕ) : WithTop ℕ)
      if start + ((p : ℕ) : WithTop ℕ) ≤
        ((d ⟨j - k.val, by have hk := Finset.mem_Icc.mp k.property; omega⟩ : ℕ) : WithTop ℕ)
      then start + ((p : ℕ) : WithTop ℕ) else ⊤)
    min take skip
  else ⊤
termination_by j
decreasing_by
  all_goals first | omega | (have hk := Finset.mem_Icc.mp k.property; omega)

/-- The largest feasible number of on-time jobs, including zero. -/
def dp3MaxOnTime {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ) : ℕ :=
  Nat.findGreatest (fun i => dp3 B p r d i n ≠ ⊤) n

end BurnInBatch.TardyJobs
