import Mathlib
import Definitions.Def_BurnInBatch_AgreeTmax_Model
import Definitions.Def_BurnInBatch_ReleaseTmax_Model

namespace BurnInBatch.TardyJobs

/-- A batch is nonempty and has no more than `B` jobs. -/
def ValidBatch {n : ℕ} (B : ℕ) (P : Finset (Fin n)) : Prop :=
  P.Nonempty ∧ P.card ≤ B

/-- A complete one-machine batch schedule, in processing order. -/
def ValidSchedule {n : ℕ} (B : ℕ) (S : List (Finset (Fin n))) : Prop :=
  (∀ P ∈ S, ValidBatch B P) ∧
  S.Pairwise (fun P Q => Disjoint P Q) ∧
  ∀ j : Fin n, ∃ P ∈ S, j ∈ P

/-- Process a list of batches as early as their releases and the preceding batch permit. -/
def finish {n : ℕ} (p r : Fin n → ℕ) : List (Finset (Fin n)) → ℕ → ℕ
  | [], t => t
  | P :: S, t => finish p r S (max t (BurnInBatch.ReleaseTmax.batchRelease r P) + BurnInBatch.AgreeTmax.batchTime p P)

/-- Completion time of job `j`. This is used only for complete valid schedules. -/
def jobCompletionAux {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) :
    List (Finset (Fin n)) → ℕ → ℕ
  | [], _ => 0
  | P :: S, t =>
      let t' := max t (BurnInBatch.ReleaseTmax.batchRelease r P) + BurnInBatch.AgreeTmax.batchTime p P
      if j ∈ P then t' else jobCompletionAux p r j S t'

def jobCompletion {n : ℕ} (p r : Fin n → ℕ)
    (S : List (Finset (Fin n))) (j : Fin n) : ℕ :=
  jobCompletionAux p r j S 0

/-- The number of jobs completed strictly after their due dates. -/
def tardyCount {n : ℕ} (p r d : Fin n → ℕ)
    (S : List (Finset (Fin n))) : ℕ :=
  (Finset.univ.filter (fun j => d j < jobCompletion p r S j)).card

/-- The minimum number of tardy jobs over all complete valid batch schedules. -/
noncomputable def minTardy {n : ℕ} (B : ℕ) (p r d : Fin n → ℕ) : ℕ :=
  sInf { v : ℕ | ∃ S : List (Finset (Fin n)), ValidSchedule B S ∧ tardyCount p r d S = v }

/-- Definition 1: earlier batches contain no job with a later due date than a job
in a later batch. -/
def BatchEDD {n : ℕ} (d : Fin n → ℕ) (S : List (Finset (Fin n))) : Prop :=
  ∀ a b : Fin S.length, a < b →
    ∀ i ∈ S[a], ∀ j ∈ S[b], d i ≤ d j

/-- A batch contains an interval of job indices in the given index order. -/
def Consecutive {n : ℕ} (P : Finset (Fin n)) : Prop :=
  ∃ first : ℕ, ∀ j : Fin n, j ∈ P ↔ first ≤ j.val ∧ j.val < first + P.card

/-- An optimal complete batch schedule for the number of tardy jobs. -/
def Optimal {n : ℕ} (B : ℕ) (p r d : Fin n → ℕ)
    (S : List (Finset (Fin n))) : Prop :=
  ValidSchedule B S ∧ tardyCount p r d S = minTardy B p r d

/-- The paper's equal-duration data: every job has processing time `p`. -/
def equalTime {n : ℕ} (p : ℕ) : Fin n → ℕ := fun _ => p

end BurnInBatch.TardyJobs
