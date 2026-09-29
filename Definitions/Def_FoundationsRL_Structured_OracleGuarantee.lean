import Mathlib

namespace FoundationsRL.Structured

/-- The guarantee provided by an online regression oracle for the structured bandit protocol
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Definition 7, p. 64). Given a horizon `T`, a sequence of oracle estimates
`fhat : Fin T → (S → ℝ)`, the ground-truth reward function `fstar`, and the decision-maker's
realized randomization `p : Fin T → (S → ℝ)` at each round (`p t` a probability vector over the
decision space `Π`), `OracleGuarantee T fhat fstar p EstSq` packages the event

`∑_{t=1}^T E_{π_t ∼ p_t}[(f̂_t(π_t) − f⋆(π_t))²] ≤ EstSq(F, T, δ)`

that Definition 7 asserts holds with probability at least `1 − δ`. As in the earlier contextual
bandit mission, the probability-`1 − δ` event of the source is captured here as an explicit
hypothesis on the realized run, rather than as a statement quantified over the randomness that
produces `f̂` and `p`. -/
def OracleGuarantee {S : Type*} [Fintype S] (T : ℕ) (fhat : Fin T → S → ℝ) (fstar : S → ℝ)
    (p : Fin T → S → ℝ) (EstSq : ℝ) : Prop :=
  ∑ t : Fin T, ∑ π : S, p t π * (fhat t π - fstar π) ^ 2 ≤ EstSq

end FoundationsRL.Structured
