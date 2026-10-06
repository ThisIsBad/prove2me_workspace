import Mathlib
import Definitions.Def_DelayedSWPT_Model_Instance

namespace DelayedSWPT.Model

/-- The Delayed SWPT priority (Anderson and Potts, p. 689): job `j` is preferred to job `k`
when `p_j/w_j < p_k/w_k`, ties broken by the smaller processing time and then by the smaller
index. Ratios are compared by cross-multiplication (`w > 0`). -/
def Prec {n : ℕ} (I : Instance n) (j k : Fin n) : Prop :=
  (I.p j : ℝ) * I.w k < (I.p k : ℝ) * I.w j ∨
    ((I.p j : ℝ) * I.w k = (I.p k : ℝ) * I.w j ∧ (I.p j < I.p k ∨ (I.p j = I.p k ∧ j < k)))

/-- The job of `A` chosen by a priority `prec`: scan the jobs in index order and keep the
current candidate unless the next job of `A` strictly precedes it. For the strict total order
`Prec I` this is the `Prec I`-least job of `A`; it is `none` exactly when `A` is empty.
Only `prec` between members of `A` is ever consulted. -/
def select {n : ℕ} (prec : Fin n → Fin n → Prop) [DecidableRel prec] (A : Finset (Fin n)) :
    Option (Fin n) :=
  (List.finRange n).foldl
    (fun acc k =>
      if k ∈ A then
        (match acc with
         | none => some k
         | some b => if prec k b then some k else some b)
      else acc)
    none

/-- The state of the simulation at the beginning of a unit time slot: the start times assigned
so far (`none` = not yet started) and the time `free` from which the machine is available. -/
structure State (n : ℕ) where
  start : Fin n → Option ℕ
  free : ℕ

/-- Nothing started, machine available from time `0`. -/
def initState (n : ℕ) : State n := ⟨fun _ => none, 0⟩

/-- The jobs available at time `t` in state `s`: released (`r j ≤ t`) and not yet started. -/
def available {n : ℕ} (r : Fin n → ℕ) (s : State n) (t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => r j ≤ t ∧ s.start j = none)

/-- The job selected at time `t`: if the machine is available (`s.free ≤ t`), the
highest-priority available job (if any); otherwise `none`. It depends only on the jobs with
`r j ≤ t` (online rule). -/
def choice {n : ℕ} (r : Fin n → ℕ) (prec : Fin n → Fin n → Prop) [DecidableRel prec]
    (s : State n) (t : ℕ) : Option (Fin n) :=
  if s.free ≤ t then select prec (available r s t) else none

/-- One unit time slot `[t, t + 1)` of Delayed SWPT: if the selected job `j` has `p j ≤ t`, it
starts at `t` and the machine is busy until `t + p j`; otherwise the machine stays idle during
`[t, t + 1)` and the choice is made afresh at `t + 1`. -/
def step {n : ℕ} (r p : Fin n → ℕ) (prec : Fin n → Fin n → Prop) [DecidableRel prec]
    (t : ℕ) (s : State n) : State n :=
  match choice r prec s t with
  | none => s
  | some j => if p j ≤ t then ⟨Function.update s.start j (some t), t + p j⟩ else s

/-- The state at the beginning of slot `t`, after the slots `0, 1, …` before `t`. -/
def stateAt {n : ℕ} (r p : Fin n → ℕ) (prec : Fin n → Fin n → Prop) [DecidableRel prec] :
    ℕ → State n
  | 0 => initState n
  | t + 1 => step r p prec t (stateAt r p prec t)

/-- The simulation horizon `∑ⱼ (rⱼ + 2pⱼ) + 1`; every job has started before it. -/
def horizon {n : ℕ} (r p : Fin n → ℕ) : ℕ := ∑ j, (r j + 2 * p j) + 1

/-- The state of Delayed SWPT on instance `I` at the beginning of slot `t`. -/
noncomputable def dswptState {n : ℕ} (I : Instance n) (t : ℕ) : State n :=
  @stateAt n I.r I.p (Prec I) (Classical.decRel _) t

/-- The job Delayed SWPT selects at time `t` (`none` if the machine is busy or nothing is
available). -/
noncomputable def dswptChoice {n : ℕ} (I : Instance n) (t : ℕ) : Option (Fin n) :=
  @choice n I.r (Prec I) (Classical.decRel _) (dswptState I t) t

/-- The Delayed SWPT schedule `π` (start times) on instance `I`, read off the simulation at the
horizon. -/
noncomputable def dswpt {n : ℕ} (I : Instance n) (j : Fin n) : ℕ :=
  ((dswptState I (horizon I.r I.p)).start j).getD 0

end DelayedSWPT.Model
