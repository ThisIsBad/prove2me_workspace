import Mathlib

namespace NetworkControl.Backpressure

/-- `L(U(t)) := Σ_{i=1}^L U_i(t)^2`, the quadratic Lyapunov function of a vector queue
backlog, defined just above Lemma 4.1 (p. 49, unnumbered display, §4.4). -/
noncomputable def lyapunovL {L : ℕ} (u : Fin L → ℝ) : ℝ :=
  ∑ i : Fin L, (u i) ^ 2

end NetworkControl.Backpressure
