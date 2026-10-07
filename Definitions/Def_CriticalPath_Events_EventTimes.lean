import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork

namespace CriticalPath.Events

variable {n : ℕ}

/-- Earliest event times, Kelley–Walker (1959) display (1), p. 163:
`t_0^(0) = 0`, `t_j^(0) = max [y_ij + t_i^(0) | i < j, (i,j) ∈ P]` for `1 ≤ j ≤ n`.
The maximum is over a nonempty set by `ProjectNetwork.pred_nonempty`; no fallback value is used. -/
noncomputable def earliest (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) : ℝ :=
  if h : j = 0 then 0
  else (N.pred j).attach.sup' (Finset.attach_nonempty_iff.2 (N.pred_nonempty h))
    (fun i => y i.1 j + earliest N y i.1)
termination_by j.val
decreasing_by exact N.lt_of_mem_pred i.2

/-- Latest event times relative to a project completion time `λ`, Kelley–Walker (1959)
display (2), p. 163: `t_n^(1) = λ`, `t_i^(1) = min [t_j^(1) − y_ij | i < j, (i,j) ∈ P]`
for `0 ≤ i ≤ n − 1`. The minimum is over a nonempty set by `ProjectNetwork.succ_nonempty`. -/
noncomputable def latest (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) (lam : ℝ)
    (i : Fin (n + 1)) : ℝ :=
  if h : i = Fin.last n then lam
  else (N.succ i).attach.inf' (Finset.attach_nonempty_iff.2 (N.succ_nonempty h))
    (fun j => latest N y lam j.1 - y i j.1)
termination_by n - i.val
decreasing_by
  have h1 := N.lt_of_mem_succ j.2
  have h2 := j.1.is_le
  rw [Fin.lt_def] at h1
  omega

/-- Maximum time available for job `(i, j)`: `t_j^(1) − t_i^(0)` (p. 163). -/
noncomputable def maxTimeAvailable (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (lam : ℝ) (e : Fin (n + 1) × Fin (n + 1)) : ℝ :=
  latest N y lam e.2 - earliest N y e.1

/-- A job is critical if its maximum time available equals its duration (p. 163). -/
def IsCritical (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) (lam : ℝ)
    (e : Fin (n + 1) × Fin (n + 1)) : Prop :=
  maxTimeAvailable N y lam e = y e.1 e.2

/-- A job is a floater if its maximum time available exceeds its duration (p. 163). -/
def IsFloater (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) (lam : ℝ)
    (e : Fin (n + 1) × Fin (n + 1)) : Prop :=
  y e.1 e.2 < maxTimeAvailable N y lam e

/-- A critical path (p. 163): a contiguous path of critical jobs through the project diagram
from origin to terminus, given as its list of events `v_0 = 0, v_1, …, v_k = n`, every
consecutive pair `(v_{r-1}, v_r)` being a job of `P` that is critical. -/
def IsCriticalPath (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) (lam : ℝ)
    (p : List (Fin (n + 1))) : Prop :=
  p.head? = some 0 ∧ p.getLast? = some (Fin.last n) ∧
    p.IsChain (fun i j => (i, j) ∈ N.P ∧ IsCritical N y lam (i, j))

end CriticalPath.Events
