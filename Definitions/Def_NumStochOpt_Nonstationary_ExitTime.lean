import Mathlib

namespace NumStochOpt.Nonstationary

/-- The exit time `τ = min {s | s ≥ s₀, ‖x^s - x^{s₀}‖ > ε}` of a sequence `x` from the closed
`ε`-ball around `x^{s₀}` (Theorem 6.4 (2)(b), p. 155, in the reading fixed by the proof of
Theorem 6.3, p. 156). When the sequence never leaves the ball the set is empty and the value is
the junk value `0`; Theorem 6.4 only evaluates it where the set is nonempty. -/
noncomputable def exitTime {n : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin n)) (s₀ : ℕ) (ε : ℝ) : ℕ :=
  sInf {s : ℕ | s₀ ≤ s ∧ ε < ‖x s - x s₀‖}

end NumStochOpt.Nonstationary
