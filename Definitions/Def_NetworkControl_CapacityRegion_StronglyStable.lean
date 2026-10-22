import Mathlib

namespace NetworkControl.CapacityRegion

/-- Definition 3.1 (p. 24). A queue backlog sequence `U` (with `U t` interpreted as `E{U(t)}`,
the expected backlog in slot `t`) is strongly stable if it has a bounded time-average:
`limsup_{t→∞} (1/t) Σ_{τ=0}^{t-1} E{U(τ)} < ∞`. For a real-valued sequence this finite-limsup
condition is exactly equivalent to the Cesàro average being bounded above for every `t`
(any finite prefix of a real sequence is automatically bounded, so an eventual bound and a
global bound agree here); we state that equivalent, quantifier-light form directly. -/
def StronglyStable (U : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ t : ℕ, (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, U τ ≤ M

end NetworkControl.CapacityRegion
