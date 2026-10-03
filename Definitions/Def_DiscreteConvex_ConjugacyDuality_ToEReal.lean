import Mathlib

/-!
The embedding `R ∪ {+∞} ↪ R ∪ {±∞}`, used throughout the discrete Legendre-Fenchel transform
(Murota, *Discrete Convex Analysis*, SIAM 2003, Chapter 8), in
`DiscreteConvex.ConjugacyDuality`.
-/

namespace DiscreteConvex.ConjugacyDuality

/-- The canonical embedding `WithTop ℝ → EReal` (`EReal = WithBot (WithTop ℝ)`), sending
`⊤ ↦ ⊤` and `(r:ℝ) ↦ (r:EReal)`. -/
def ToEReal (v : WithTop ℝ) : EReal :=
  WithBot.some v

end DiscreteConvex.ConjugacyDuality
