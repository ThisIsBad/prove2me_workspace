import Mathlib

namespace YoungConventions.AdaptivePlay

/-- **The state space `H` of adaptive play** (Young 1993, *The Evolution of Conventions*,
Econometrica 61:57–84, §3, p. 61, PDF p. 6): "a finite Markov chain on the state space `H`
consisting of all sequences of length `m` drawn from `∏Sᵢ`".

A state `h : History S m` is a sequence of `m` plays (strategy tuples).

**Formalization Note.** Positions are `Fin m`, read left to right: position `0` is the **oldest**
(left-most) play and position `m − 1` the most recent (right-most) play, as in the paper's
`h = (s(t − m + 1), …, s(t))`. -/
abbrev History {ι : Type*} (S : ι → Type*) (m : ℕ) : Type _ :=
  Fin m → ∀ i, S i

end YoungConventions.AdaptivePlay
