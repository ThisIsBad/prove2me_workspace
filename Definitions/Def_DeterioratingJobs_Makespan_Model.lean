import Mathlib

namespace DeterioratingJobs.Makespan

open MeasureTheory

/-- Linear deterioration (Browne–Yechiali 1990, p. 495): if job `j` is started at time `t`, its
actual processing time is `Y_j(t) = X_j + α_j t`, where `X_j` is its initial processing requirement
and `α_j` its growth rate. The job stops deteriorating once it is put on the processor. -/
def actualProcessingTime {Ω : Type*} {N : ℕ} (X : Fin N → Ω → ℝ) (α : Fin N → ℝ)
    (j : Fin N) (t : ℝ) (ω : Ω) : ℝ :=
  X j ω + α j * t

/-- Completion times under the nonpreemptive, non-idling schedule `π` (Browne–Yechiali 1990,
pp. 495–496). `π k` is the job processed in position `k` (0-based: the paper's `π(k+1)`).
`completionTime X α π k ω` is the completion time `S_k` of the `k`-th processed job, defined by the
model recursion `S_0 = 0`, `S_{k+1} = S_k + Y_{π(k)}(S_k)`: the job in position `k` starts at `S_k`
and takes `X_{π(k)} + α_{π(k)} S_k`. For `k ≥ N` there is no further job and `S` stays constant. -/
def completionTime {Ω : Type*} {N : ℕ} (X : Fin N → Ω → ℝ) (α : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun ω =>
      if h : k < N then
        completionTime X α π k ω +
          actualProcessingTime X α (π ⟨k, h⟩) (completionTime X α π k ω) ω
      else completionTime X α π k ω

/-- The makespan `S_N(π)`: the completion time of the last of the `N` jobs under `π`. -/
def makespan {Ω : Type*} {N : ℕ} (X : Fin N → Ω → ℝ) (α : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (ω : Ω) : ℝ :=
  completionTime X α π N ω

/-- The expected makespan `E S_N(π)` under the probability measure `P`. -/
noncomputable def expectedMakespan {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ}
    (X : Fin N → Ω → ℝ) (α : Fin N → ℝ) (π : Equiv.Perm (Fin N)) : ℝ :=
  ∫ ω, makespan X α π ω ∂P

end DeterioratingJobs.Makespan
