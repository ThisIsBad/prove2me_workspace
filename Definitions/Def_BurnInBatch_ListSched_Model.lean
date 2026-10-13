import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan

namespace BurnInBatch.ListSched

/-- A batch has the processing time of its longest member. -/
noncomputable def batchTime {n : ℕ} (p : Fin n → ℝ) (P : Finset (Fin n)) : ℝ :=
  if h : P.Nonempty then P.sup' h p else 0

/-- An ordered partition of exactly `J` into nonempty batches of capacity at most `B`. -/
def ValidBatching {n : ℕ} (B : ℕ) (J : Finset (Fin n))
    (S : List (Finset (Fin n))) : Prop :=
  (∀ P ∈ S, P.Nonempty ∧ P.card ≤ B) ∧
  S.Pairwise Disjoint ∧
  S.foldr (· ∪ ·) ∅ = J

/-- The processing time of batch position `k`, extended by zero past the list. -/
noncomputable def batchTimes {n : ℕ} (p : Fin n → ℝ)
    (S : List (Finset (Fin n))) (k : ℕ) : ℝ :=
  if h : k < S.length then batchTime p (S[k]) else 0

/-- A parallel schedule consists of an ordered valid batching and a machine for each batch. -/
structure ParallelSchedule {n : ℕ} (B m : ℕ) (J : Finset (Fin n)) where
  batches : List (Finset (Fin n))
  valid : ValidBatching B J batches
  machine : Fin batches.length → Fin m

/-- Each machine works through its batches in list order, without inserted idle time. -/
noncomputable def batchCompletion {n m : ℕ} (p : Fin n → ℝ)
    (S : List (Finset (Fin n))) (σ : Fin S.length → Fin m)
    (k : Fin S.length) : ℝ :=
  ∑ t : Fin S.length,
    if (t : ℕ) ≤ (k : ℕ) ∧ σ t = σ k then batchTime p S[t] else 0

/-- Completion of a job in its unique batch in a valid schedule. -/
noncomputable def jobCompletion {n m : ℕ} (p : Fin n → ℝ)
    (S : List (Finset (Fin n))) (σ : Fin S.length → Fin m)
    (j : Fin n) : ℝ :=
  if h : (Finset.univ.filter (fun k : Fin S.length => j ∈ S[k])).Nonempty then
    (Finset.univ.filter (fun k : Fin S.length => j ∈ S[k])).sup' h
      (batchCompletion p S σ)
  else 0

/-- Maximum job lateness for a schedule of `J`; the empty set has value zero. -/
noncomputable def scheduleLateness {n m : ℕ} (p d : Fin n → ℝ)
    (J : Finset (Fin n)) (S : List (Finset (Fin n)))
    (σ : Fin S.length → Fin m) : ℝ :=
  if h : J.Nonempty then J.sup' h (fun j => jobCompletion p S σ j - d j) else 0

/-- The optimum makespan ranges over every valid batching and every assignment. -/
noncomputable def CmaxStar {n : ℕ} (p : Fin n → ℝ) (B m : ℕ)
    (J : Finset (Fin n)) : ℝ :=
  ⨅ S : { S : List (Finset (Fin n)) // ValidBatching B J S },
    NumStochOpt.ListScheduling.optMakespan S.val.length m (batchTimes p S.val)

/-- The optimum maximum lateness ranges over every valid parallel batch schedule. -/
noncomputable def LStar {n : ℕ} (p d : Fin n → ℝ) (B m : ℕ)
    (J : Finset (Fin n)) : ℝ :=
  ⨅ G : ParallelSchedule B m J,
    scheduleLateness p d J G.batches G.machine

/-- BLS takes consecutive full chunks of an arbitrary list of jobs. -/
def blsBatches {n : ℕ} (B : ℕ) (l : List (Fin n)) : List (Finset (Fin n)) :=
  (l.toChunks B).map List.toFinset

/-- A list contains precisely the jobs in `J`, each once. -/
def ListsJobs {n : ℕ} (J : Finset (Fin n)) (l : List (Fin n)) : Prop :=
  l.Nodup ∧ ∀ j, j ∈ l ↔ j ∈ J

/-- BLS assigns each batch to the least loaded machine; labels break ties. -/
noncomputable def blsMachine {n : ℕ} (p : Fin n → ℝ) (B m : ℕ)
    (hm : 0 < m) (l : List (Fin n)) (k : Fin (blsBatches B l).length) : Fin m :=
  (NumStochOpt.ListScheduling.firstAvailable
    (NumStochOpt.ListScheduling.lsLoads m (batchTimes p (blsBatches B l)) k)).getD ⟨0, hm⟩

/-- The BLS makespan is the published list-scheduling makespan of batch lengths. -/
noncomputable def blsMakespan {n : ℕ} (p : Fin n → ℝ) (B m : ℕ)
    (l : List (Fin n)) : ℝ :=
  NumStochOpt.ListScheduling.listMakespan (blsBatches B l).length m
    (batchTimes p (blsBatches B l))

/-- BLS maximum lateness, computed from the completion of each job's batch. -/
noncomputable def blsLateness {n : ℕ} (p d : Fin n → ℝ) (B m : ℕ)
    (hm : 0 < m) (l : List (Fin n)) (J : Finset (Fin n)) : ℝ :=
  scheduleLateness p d J (blsBatches B l) (blsMachine p B m hm l)

/-- The first `k + 1` BLS batches, expressed as their prefix of the job list. -/
def blsPrefix {n : ℕ} (B : ℕ) (l : List (Fin n)) (k : ℕ) : List (Fin n) :=
  l.take ((k + 1) * B)

/-- All jobs in the first `k + 1` BLS batches. -/
def blsPrefixJobs {n : ℕ} (B : ℕ) (l : List (Fin n)) (k : ℕ) : Finset (Fin n) :=
  (blsPrefix B l k).toFinset

/-- The largest due date of the full, nonempty instance. -/
noncomputable def maxDue {n : ℕ} (d : Fin n → ℝ) (hn : 0 < n) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)) d

end BurnInBatch.ListSched
