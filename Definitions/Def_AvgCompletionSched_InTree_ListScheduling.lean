import Mathlib
import Definitions.Def_AvgCompletionSched_InTree_Model

namespace AvgCompletionSched.InTree

variable {n m : ℕ}

/-- Job `j` is ready at time `t` in the schedule `G`: every predecessor of `j` has completed by
time `t` (there are no release dates). -/
def IsReady {I : Instance n} (G : Schedule I m) (j : Fin n) (t : ℝ) : Prop :=
  ∀ i, I.prec i j → G.C i ≤ t

/-- All `m` machines are busy at time `t` in the schedule `G`: every machine `μ` is processing
some job `k` at time `t`, i.e. `S_k ≤ t < C_k`. -/
def AllBusy {I : Instance n} (G : Schedule I m) (t : ℝ) : Prop :=
  ∀ μ : Fin m, ∃ k, G.M k = μ ∧ G.S k ≤ t ∧ t < G.C k

/-- `G` is a list schedule for the list `π` in the sense of footnote 3 (p. 158) and §4.4
(p. 162): whenever a machine is free, the first ready job in the list is started on it
(Graham's list scheduling). Up to the labelling of machines this is captured by two rules:
1. no unforced idleness: if a job `j` is ready at time `t ≥ 0` but has not started yet
   (`t < S_j`), then all `m` machines are busy at `t`;
2. list priority: if a job `l` starts at time `S_l` and another job `j` that starts later is
   already ready at `S_l`, then `l` comes before `j` in the list. -/
def IsListSchedule (I : Instance n) (π : Fin n ≃ Fin n) (G : Schedule I m) : Prop :=
  (∀ j (t : ℝ), 0 ≤ t → t < G.S j → IsReady G j t → AllBusy G t) ∧
  (∀ l j, G.S l < G.S j → IsReady G j (G.S l) → π.symm l < π.symm j)

end AvgCompletionSched.InTree
