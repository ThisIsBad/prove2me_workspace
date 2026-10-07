import Mathlib

namespace RandomGradFree.Nonsmooth

/-- `z` is a Euclidean projection of `y` onto `Q`: `z ∈ Q` and `z` is a nearest point of `Q`
to `y`. For a nonempty closed convex `Q` in a finite-dimensional inner product space such a
`z` exists and is unique; it is the paper's `π_Q(y)` (p. 541). -/
def IsMetricProjection {E : Type*} [NormedAddCommGroup E] (Q : Set E) (y z : E) : Prop :=
  z ∈ Q ∧ ∀ w ∈ Q, ‖y - z‖ ≤ ‖y - w‖

end RandomGradFree.Nonsmooth
