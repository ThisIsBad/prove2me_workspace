import Mathlib

namespace NetworkControl.CapacityRegion

/-- The discrete-time queueing law stated at the start of Section 3.1 (p. 23):
`U(t+1) = max[U(t) - μ(t), 0] + A(t)`, for an arrival process `A`, a service process `svc`,
and an initial backlog `U0`, all on a common sample space `Ω`. -/
def QueueBacklog {Ω : Type*} (A svc : ℕ → Ω → ℝ) (U0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => U0
  | t + 1 => fun ω => max (QueueBacklog A svc U0 t ω - svc t ω) 0 + A t ω

end NetworkControl.CapacityRegion
