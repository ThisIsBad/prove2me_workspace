import Mathlib
import Definitions.Def_BurnInBatch_TardyJobs_Model

namespace BurnInBatch.TardyJobs

/-- The §4 extension of DP3 to job-dependent processing times and no release times.
For a consecutive last on-time batch ending at job `j`, its duration is `p_j`. -/
def dp3Variable {n : ℕ} (B : ℕ) (p d : Fin n → ℕ) (i j : ℕ) : WithTop ℕ :=
  if hi0 : i = 0 then 0
  else if hgt : i > j then ⊤
  else if hj : j ≤ n then
    have hi : i ≤ j := by omega
    have hjpos : 0 < j := by omega
    let skip := dp3Variable B p d i (j - 1)
    let take := (Finset.Icc 1 (min B i)).attach.inf (fun k =>
      let finish := dp3Variable B p d (i - k.val) (j - k.val) +
        ((p ⟨j - 1, by omega⟩ : ℕ) : WithTop ℕ)
      if finish ≤
        ((d ⟨j - k.val, by have hk := Finset.mem_Icc.mp k.property; omega⟩ : ℕ) : WithTop ℕ)
      then finish else ⊤)
    min take skip
  else ⊤
termination_by j
decreasing_by
  all_goals first | omega | (have hk := Finset.mem_Icc.mp k.property; omega)

def dp3VariableMaxOnTime {n : ℕ} (B : ℕ) (p d : Fin n → ℕ) : ℕ :=
  Nat.findGreatest (fun i => dp3Variable B p d i n ≠ ⊤) n

end BurnInBatch.TardyJobs
