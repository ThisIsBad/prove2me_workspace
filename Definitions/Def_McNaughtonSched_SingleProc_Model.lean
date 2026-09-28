import Mathlib

namespace McNaughtonSched.SingleProc

/-- One piece of work on the single processor: task `task` is processed during the time
interval from `start` to `stop`. Tasks (1), …, (m) of McNaughton (1959), §2, p. 4, are the
zero-based indices of `Fin m`. A task done in several parts ("split", p. 4) has several
pieces. -/
structure Piece (m : ℕ) where
  task : Fin m
  start : ℝ
  stop : ℝ

/-- A schedule for the single processor is a finite list of pieces; a task "may be split in
any number of parts" (p. 4), finitely many. -/
abbrev Schedule (m : ℕ) := List (Piece m)

variable {m : ℕ}

/-- Two pieces occupy disjoint time intervals (touching endpoints allowed). -/
def Piece.Disjoint (g h : Piece m) : Prop := g.stop ≤ h.start ∨ h.stop ≤ g.start

/-- The total processing time that schedule `S` gives to task `i`: the summed lengths of its
pieces. -/
noncomputable def processed (S : Schedule m) (i : Fin m) : ℝ :=
  ((S.filter fun g => g.task = i).map fun g => g.stop - g.start).sum

/-- A feasible schedule for processing times `a`: every piece lies in `[0, ∞)` (time `0` is
"the present", p. 4) and has `start ≤ stop`; no two pieces overlap in time (one processor);
and every task `i` receives exactly `a i` units of processing time. -/
def IsFeasible (a : Fin m → ℝ) (S : Schedule m) : Prop :=
  (∀ g ∈ S, 0 ≤ g.start ∧ g.start ≤ g.stop) ∧
    S.Pairwise Piece.Disjoint ∧
    ∀ i, processed S i = a i

/-- The completion time of task `i` in `S`: the latest stop time of one of its pieces
(`0` if it has none, which feasibility with `a i > 0` excludes). -/
noncomputable def completion (S : Schedule m) (i : Fin m) : ℝ :=
  ((S.filter fun g => g.task = i).map Piece.stop).foldr max 0

/-- The loss on task `i` when it is completed at time `t`: `p_i x`, where `x` is the number
of units of time from the deadline `d_i` to the completion, and no loss if the task is
finished at or before `d_i` (p. 4). -/
noncomputable def taskLoss (p d : Fin m → ℝ) (i : Fin m) (t : ℝ) : ℝ :=
  p i * max 0 (t - d i)

/-- The total loss of schedule `S` with penalties `p` and deadlines `d`. -/
noncomputable def totalLoss (p d : Fin m → ℝ) (S : Schedule m) : ℝ :=
  ∑ i, taskLoss p d i (completion S i)

/-- No task is split: every task is processed in exactly one piece. -/
def NoSplit (S : Schedule m) : Prop :=
  ∀ i, (S.filter fun g => g.task = i).length = 1

/-- The unsplit schedule without unused time that processes the tasks in the order `σ`
(`σ k` is the task in position `k`, positions being the zero-based indices of `Fin m`): task `σ k` runs from
`∑_{l<k} a (σ l)` to `∑_{l≤k} a (σ l)`. -/
noncomputable def seqSchedule (a : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) : Schedule m :=
  List.ofFn fun k : Fin m =>
    { task := σ k
      start := ∑ l ∈ Finset.univ.filter (fun l : Fin m => l < k), a (σ l)
      stop := ∑ l ∈ Finset.univ.filter (fun l : Fin m => l ≤ k), a (σ l) }

/-- The order `σ` lists the tasks in order of decreasing (non-increasing) ratio
`r_i = p_i / a_i` (p. 4): an earlier position never has a smaller ratio. Ties are allowed in
any order. -/
def InRatioOrder (a p : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) : Prop :=
  ∀ k l : Fin m, k ≤ l → p (σ l) / a (σ l) ≤ p (σ k) / a (σ k)

end McNaughtonSched.SingleProc
