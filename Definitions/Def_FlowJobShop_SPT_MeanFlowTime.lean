import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance

namespace FlowJobShop.SPT

open JobShopLTAS.Core

variable {m n : ℕ}

/-- Feasibility in the job-shop model of Gonzalez–Sahni (p. 36). A zero-time task has an
instantaneous completion and occupies no processor interval; only positive-time tasks can
overlap on a processor. -/
structure IsPaperFeasibleSchedule (inst : Instance m n) (s : inst.Op → ℝ) : Prop where
  start_nonneg : ∀ o : inst.Op, 0 ≤ s o
  precedence : ∀ j : Fin n, ∀ i i' : Fin (inst.μ j), i.val + 1 = i'.val →
    s ⟨j, i⟩ + inst.p j i ≤ s ⟨j, i'⟩
  machine_disjoint : ∀ o o' : inst.Op, o ≠ o' → inst.mach o = inst.mach o' →
    0 < inst.proc o → 0 < inst.proc o' →
      s o + inst.proc o ≤ s o' ∨ s o' + inst.proc o' ≤ s o

/-- The finish time `f_j(s)` of job `j` in the schedule `s` (Gonzalez–Sahni 1978, p. 36): the time
at which all tasks of job `j` have been completed, i.e. the largest completion time
`s ⟨j, i⟩ + p j i` over the tasks `i` of job `j`. The schedule starts at time zero, so the
maximum is taken with baseline `0`; a job without tasks has finish time `0`. -/
noncomputable def finishTime (inst : Instance m n) (s : inst.Op → ℝ) (j : Fin n) : ℝ :=
  Finset.univ.fold max 0 (fun i : Fin (inst.μ j) => s ⟨j, i⟩ + inst.p j i)

/-- The mean flow time `MFT(s) = (∑_j f_j(s)) / n` of the schedule `s` (p. 36). For `n = 0` Lean's
division gives `0`, which is the empty average. -/
noncomputable def meanFlowTime (inst : Instance m n) (s : inst.Op → ℝ) : ℝ :=
  (∑ j, finishTime inst s j) / n

/-- The flow shop with task times `t k i ≥ 0` (task `k` of job `i` runs on processor `P_k` for
`t k i`, p. 36), viewed as a job shop: every job has `m` tasks, and task `k` is on processor `k`. -/
def flowShop (t : Fin m → Fin n → ℝ) (ht : ∀ k i, 0 ≤ t k i) : Instance m n where
  μ := fun _ => m
  π := fun _ k => k
  p := fun i k => t k i
  p_nonneg := fun i k => ht k i

end FlowJobShop.SPT
