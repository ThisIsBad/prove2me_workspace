import Mathlib

namespace FoundationsRL.Contextual

/-- The guarantee provided by an online regression oracle (Foster & Rakhlin, *Foundations of
Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Definition 3,
p. 47). Given a context sequence `x : Fin T → X`, the ground-truth reward function `fstar`,
a sequence of oracle estimates `fhat : Fin T → X → Fin A → ℝ`, and the decision-maker's
realized randomization `p : Fin T → Fin A → ℝ` at each round (`p t` a probability vector over
`Fin A`), `OracleGuarantee A T x fhat fstar p EstSq` packages the event

`∑_{t=1}^T E_{π_t ∼ p_t}[(fhat_t(x_t, π_t) - fstar(x_t, π_t))^2] ≤ EstSq(F, T, δ)`

that Definition 3 asserts holds with probability at least `1 - δ`. Every result in this
mission (Propositions 8-10) is a purely algebraic consequence of this bound once it holds, so
the probability-`1 - δ` event of the source is captured here as an explicit hypothesis on
the realized run, rather than as a statement quantified over the randomness that produces
`fhat` and `p`. -/
def OracleGuarantee {X : Type*} (A T : ℕ) (x : Fin T → X) (fhat : Fin T → X → Fin A → ℝ)
    (fstar : X → Fin A → ℝ) (p : Fin T → Fin A → ℝ) (EstSq : ℝ) : Prop :=
  ∑ t : Fin T, ∑ a : Fin A, p t a * (fhat t (x t) a - fstar (x t) a) ^ 2 ≤ EstSq

end FoundationsRL.Contextual
