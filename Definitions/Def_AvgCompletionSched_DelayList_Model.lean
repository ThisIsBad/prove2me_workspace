import Mathlib

namespace AvgCompletionSched.DelayList

/-- An instance of weighted completion time scheduling with release dates and precedence
constraints (Chekuri–Motwani–Natarajan–Stein 2001, §1, pp. 146–147, and §4, pp. 157–158):
`n` jobs `0, …, n-1`; job `j` has processing time `p j > 0`, release date `r j ≥ 0` and weight
`w j > 0`. The precedence constraints are given by a strict partial order `prec` on the jobs
(`prec i j` means `i ≺ j`: job `i` must be completed before job `j` starts); the DAG of the paper
is represented by its transitive closure. The number of machines is not part of the instance. -/
structure Instance (n : ℕ) where
  /-- processing times -/
  p : Fin n → ℝ
  /-- release dates -/
  r : Fin n → ℝ
  /-- weights -/
  w : Fin n → ℝ
  /-- precedence relation: `prec i j` means `i ≺ j` -/
  prec : Fin n → Fin n → Prop
  p_pos : ∀ j, 0 < p j
  r_nonneg : ∀ j, 0 ≤ r j
  w_pos : ∀ j, 0 < w j
  prec_irrefl : ∀ j, ¬ prec j j
  prec_trans : ∀ i j k, prec i j → prec j k → prec i k

variable {n : ℕ}

open Classical in
/-- The predecessors of job `j`: the jobs `i` with `i ≺ j`. -/
noncomputable def Instance.preds (I : Instance n) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => I.prec i j

/-- The precedence relation of an instance is well founded (a finite strict partial order). -/
theorem Instance.prec_wf (I : Instance n) : WellFounded I.prec :=
  @Finite.wellFounded_of_trans_of_irrefl _ _ I.prec ⟨I.prec_trans⟩ ⟨I.prec_irrefl⟩

/-- Definition 4.1 (p. 158): the critical-path length `κ_j`, defined recursively along the
precedence order. For a job `j` with no predecessors `κ_j = p_j + r_j`; otherwise
`κ_j = p_j + max {max_{i ≺ j} κ_i, r_j}`. -/
noncomputable def kappa (I : Instance n) : Fin n → ℝ :=
  I.prec_wf.fix fun j IH =>
    if h : (I.preds j).Nonempty then
      I.p j + max ((I.preds j).attach.sup' (Finset.attach_nonempty_iff.mpr h)
        fun i => IH i.1 (by simpa [Instance.preds] using i.2)) (I.r j)
    else I.p j + I.r j

/-- A feasible nonpreemptive schedule of the instance on `m` machines: job `j` runs without
interruption on machine `M j` during `[S j, S j + p j)`; it does not start before its release
date; two different jobs on the same machine do not overlap; and if `i ≺ j` then `j` starts no
earlier than `i` completes. A one-machine schedule is a schedule with `m = 1`. -/
structure Schedule (I : Instance n) (m : ℕ) where
  /-- start times -/
  S : Fin n → ℝ
  /-- machine assignment -/
  M : Fin n → Fin m
  released : ∀ j, I.r j ≤ S j
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

/-- The list `π` is the one-machine schedule `S1` taken as a list (p. 158): the jobs in order of
their completion times in `S1`. -/
def IsCompletionOrder {I : Instance n} (S1 : Schedule I 1) (π : Fin n ≃ Fin n) : Prop :=
  ∀ k l : Fin n, k ≤ l → S1.C (π k) ≤ S1.C (π l)

end AvgCompletionSched.DelayList
