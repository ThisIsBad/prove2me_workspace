import Mathlib

namespace AvgCompletionSched.InTree

/-- An instance of weighted completion time scheduling with in-tree precedence constraints and
no release dates (Chekuri–Motwani–Natarajan–Stein 2001, §1, pp. 146–147, and §4.4, p. 162):
`n` jobs `0, …, n-1`; job `j` has processing time `p j > 0` and weight `w j > 0`; every job is
available at time `0`. The in-tree (more generally in-forest) precedence structure is given by
the unique immediate successor `succ j` of each job (`none` if `j` has no successor): in an
in-tree a node has at most one immediate successor. The successor graph has no cycles. The
number of machines is not part of the instance. -/
structure Instance (n : ℕ) where
  /-- processing times -/
  p : Fin n → ℝ
  /-- weights -/
  w : Fin n → ℝ
  /-- the immediate successor of each job, if any -/
  succ : Fin n → Option (Fin n)
  p_pos : ∀ j, 0 < p j
  w_pos : ∀ j, 0 < w j
  acyclic : ∀ j, ¬ Relation.TransGen (fun a b => succ a = some b) j j

variable {n : ℕ}

/-- The precedence relation `i ≺ j`: `j` is reached from `i` by following immediate successors
one or more times (the transitive closure of the in-tree's edges `i → succ i`). -/
def Instance.prec (I : Instance n) (i j : Fin n) : Prop :=
  Relation.TransGen (fun a b => I.succ a = some b) i j

/-- The precedence relation of an instance is well founded (a finite strict partial order). -/
theorem Instance.prec_wf (I : Instance n) : WellFounded I.prec :=
  @Finite.wellFounded_of_trans_of_irrefl _ _ I.prec
    ⟨fun _ _ _ h₁ h₂ => Relation.TransGen.trans h₁ h₂⟩ ⟨I.acyclic⟩

open Classical in
/-- The predecessors of job `j`: the jobs `i` with `i ≺ j`. -/
noncomputable def Instance.preds (I : Instance n) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => I.prec i j

/-- Definition 4.1 (p. 158) with all release dates equal to `0`: the critical-path length
`κ_j`, defined recursively along the precedence order. For a job `j` with no predecessors
`κ_j = p_j`; otherwise `κ_j = p_j + max_{i ≺ j} κ_i`. -/
noncomputable def kappa (I : Instance n) : Fin n → ℝ :=
  I.prec_wf.fix fun j IH =>
    if h : (I.preds j).Nonempty then
      I.p j + (I.preds j).attach.sup' (Finset.attach_nonempty_iff.mpr h)
        fun i => IH i.1 (by simpa [Instance.preds] using i.2)
    else I.p j

/-- A feasible nonpreemptive schedule of the instance on `m` identical machines: job `j` runs
without interruption on machine `M j` during `[S j, S j + p j)`; no job starts before time `0`
(there are no release dates); two different jobs on the same machine do not overlap; and if
`i ≺ j` then `j` starts no earlier than `i` completes. -/
structure Schedule (I : Instance n) (m : ℕ) where
  /-- start times -/
  S : Fin n → ℝ
  /-- machine assignment -/
  M : Fin n → Fin m
  nonneg : ∀ j, 0 ≤ S j
  noOverlap : ∀ i j, M i = M j → i ≠ j → S i + I.p i ≤ S j ∨ S j + I.p j ≤ S i
  precedence : ∀ i j, I.prec i j → S i + I.p i ≤ S j

/-- Completion time `C_j = S_j + p_j` of job `j` in a nonpreemptive schedule. -/
def Schedule.C {I : Instance n} {m : ℕ} (N : Schedule I m) (j : Fin n) : ℝ :=
  N.S j + I.p j

/-- The objective value of a schedule: the sum of weighted completion times `∑_j w_j C_j`. -/
noncomputable def Schedule.wct {I : Instance n} {m : ℕ} (N : Schedule I m) : ℝ :=
  ∑ j, I.w j * N.C j

/-- A list of the jobs, `π k` being the `k`-th job of the list, obeys the precedence constraints
(footnote 2, p. 158): if `i ≺ j` then `i` comes earlier in the list than `j`. -/
def ObeysPrecedence (I : Instance n) (π : Fin n ≃ Fin n) : Prop :=
  ∀ i j, I.prec i j → π.symm i < π.symm j

/-- The idle-free one-machine schedule `S¹` that processes the jobs in the order of the list
`π`: the completion time of job `j` is the total processing time of the jobs up to and
including `j` in the list, `C¹_j = ∑_{k ≤ pos(j)} p_{π k}`. -/
noncomputable def oneMachineC (I : Instance n) (π : Fin n ≃ Fin n) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => k ≤ π.symm j), I.p (π k)

/-- The sum of weighted completion times `C¹ = ∑_j w_j C¹_j` of the one-machine schedule in the
order `π`. -/
noncomputable def oneMachineWct (I : Instance n) (π : Fin n ≃ Fin n) : ℝ :=
  ∑ j, I.w j * oneMachineC I π j

/-- `π` is an optimal one-machine schedule: it obeys the precedence constraints, and no
precedence-respecting order has a smaller sum of weighted completion times. (With no release
dates and positive processing times, idle time never helps, so optimal one-machine schedules are
idle-free and determined by their order.) -/
def IsOptimalOneMachine (I : Instance n) (π : Fin n ≃ Fin n) : Prop :=
  ObeysPrecedence I π ∧ ∀ σ : Fin n ≃ Fin n, ObeysPrecedence I σ → oneMachineWct I π ≤ oneMachineWct I σ

end AvgCompletionSched.InTree
