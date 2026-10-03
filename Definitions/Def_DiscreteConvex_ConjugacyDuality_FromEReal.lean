import Mathlib

/-!
The projection from `R ∪ {±∞}` to `R ∪ {+∞}`, used to view a discrete Legendre-Fenchel
transform (whose raw supremum lands in `EReal`) as a function of the same type as the M-convex
and L-convex functions it is compared against (Murota, *Discrete Convex Analysis*, SIAM 2003,
p.212, Eq. (8.11)), in `DiscreteConvex.ConjugacyDuality`.
-/

namespace DiscreteConvex.ConjugacyDuality

/-- The projection `EReal → WithTop ℝ` sending `⊤ ↦ ⊤`, `(r:ℝ) ↦ (r:WithTop ℝ)`, and `⊥` to the
junk value `⊤` (never produced by a discrete Legendre-Fenchel transform of a function with
nonempty effective domain, since the supremum defining it is then never taken over an empty
set). -/
def FromEReal (v : EReal) : WithTop ℝ :=
  WithBot.unbotD ⊤ v

end DiscreteConvex.ConjugacyDuality
