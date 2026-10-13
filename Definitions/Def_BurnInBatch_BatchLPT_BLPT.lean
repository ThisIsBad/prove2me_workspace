import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_BurnInBatch_BatchLPT_Model

namespace BurnInBatch.BatchLPT

open NumStochOpt.ListScheduling

/-- Step 1 of Algorithm BLPT (p. 772), ranking: `l` lists every job exactly once, in
nonincreasing order of processing time (ties in any order). -/
def IsLPTList {n : ℕ} (p : Fin n → ℝ) (l : List (Fin n)) : Prop :=
  l.Perm (List.finRange n) ∧ l.Pairwise (fun a b => p b ≤ p a)

/-- Step 1 of Algorithm BLPT, batching: successive groups of `B` jobs of the ranked list
`l` (the last group possibly smaller). -/
def blptBatches {n : ℕ} (B : ℕ) (l : List (Fin n)) : List (Finset (Fin n)) :=
  (l.toChunks B).map List.toFinset

/-- Step 2 of Algorithm BLPT, ordering: `bl` lists the batches of Step 1, each once, in
nonincreasing order of batch time (equal-time batches in any order). -/
def IsBLPTOrder {n : ℕ} (p : Fin n → ℝ) (B : ℕ) (l : List (Fin n))
    (bl : List (Finset (Fin n))) : Prop :=
  bl.Perm (blptBatches B l) ∧ bl.Pairwise (fun P Q => BurnInBatch.ListSched.batchTime p Q ≤ BurnInBatch.ListSched.batchTime p P)

/-- `C(BLPT)`: the makespan of Step 2, which assigns the ordered batches `bl` to the `m`
machines "as they become free", i.e. each next batch to a least-loaded machine (published
list scheduling `listMakespan`). -/
noncomputable def blptMakespan {n : ℕ} (m : ℕ) (p : Fin n → ℝ) (bl : List (Finset (Fin n))) : ℝ :=
  listMakespan bl.length m (BurnInBatch.ListSched.batchTimes p bl)

/-- Completion time of item `k` under list scheduling of the items `q 0, q 1, …` on `m`
machines: the load of the machine it is assigned to, before it, plus its own time. -/
noncomputable def lsCompletion (m : ℕ) (q : ℕ → ℝ) (k : ℕ) : ℝ :=
  match firstAvailable (lsLoads m q k) with
  | some i => lsLoads m q k i + q k
  | none => 0

/-- `L`, the maximum lateness `max_j (C_j - d_j)` of the BLPT schedule of the ordered
batches `bl`, a job completing with its batch. -/
noncomputable def blptLmax {n : ℕ} (m : ℕ) (p d : Fin n → ℝ) (bl : List (Finset (Fin n))) : ℝ :=
  ⨆ j : Fin n, (jobCompletion bl (fun k => lsCompletion m (BurnInBatch.ListSched.batchTimes p bl) k) j - d j)

end BurnInBatch.BatchLPT
