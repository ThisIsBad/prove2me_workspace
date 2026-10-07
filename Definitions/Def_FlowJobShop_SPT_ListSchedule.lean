import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance

namespace FlowJobShop.SPT

open JobShopLTAS.Core

variable {m n : ℕ}

/-- `σ` lists the jobs in an SPT order (Gonzalez–Sahni 1978, pp. 46–47): the job in position `k`
is `σ k`, and the total task times `L_j = jobLength j` are nondecreasing along the list. Ties may be
broken arbitrarily. -/
def IsSPTOrder (inst : Instance m n) (σ : Fin n ≃ Fin n) : Prop :=
  Monotone fun k => inst.jobLength (σ k)

/-- The state of the list-scheduling construction: for every processor, the latest completion
time of a task already placed on it (`0` if none), and the start times assigned so far. -/
structure ListState (inst : Instance m n) where
  avail : Fin m → ℝ
  start : inst.Op → ℝ

/-- Place task `i` of job `j`. The second component of the state is the completion time of the
job's previous task (`0` before its first task). A positive-time task starts at the later of
that time and the processor's availability. A zero-time task completes when the preceding task
completes and does not change processor availability. -/
noncomputable def placeTask (inst : Instance m n) (j : Fin n) (st : ListState inst × ℝ)
    (i : Fin (inst.μ j)) : ListState inst × ℝ :=
  let b := if inst.p j i = 0 then st.2 else max st.2 (st.1.avail (inst.π j i))
  let c := b + inst.p j i
  let avail := if inst.p j i = 0 then st.1.avail else
    Function.update st.1.avail (inst.π j i) c
  (⟨avail, Function.update st.1.start ⟨j, i⟩ b⟩, c)

/-- Place all tasks of job `j`, in their own order. -/
noncomputable def placeJob (inst : Instance m n) (st : ListState inst) (j : Fin n) :
    ListState inst :=
  ((List.finRange (inst.μ j)).foldl (placeTask inst j) (st, 0)).1

/-- The non-preemptive list schedule that processes the jobs `σ 0, σ 1, …` in turn, each
job's tasks in their own order, every task starting as soon as its job's previous task has
completed and every positive-time task already placed on its processor has completed. When `σ` is an SPT order
(`IsSPTOrder`) this is the SPT schedule of Gonzalez–Sahni 1978, pp. 46–47. -/
noncomputable def listSchedule (inst : Instance m n) (σ : Fin n ≃ Fin n) : inst.Op → ℝ :=
  ((List.finRange n).foldl (fun st k => placeJob inst st (σ k))
    (⟨fun _ => 0, fun _ => 0⟩ : ListState inst)).start

end FlowJobShop.SPT
