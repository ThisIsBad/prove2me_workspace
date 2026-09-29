import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 284, Eq. (4.2): the concave closure `ĝ(b) = inf{⟨p, b⟩ − g°(p) | p ∈ ℝ^V}` of a function
`g : B → ℝ` on a nonempty finite `B ⊆ ℤ^V` is a concave function on the convex hull `B̄` of `B`.

This is the concavity half of the Extension Theorem (Murota 1996, p. 288, Theorem 4.6): together with
`concaveClosure_eq_of_exc` (Lemma 4.5) it shows that an M-concave `ω` on an integral base set
`B` extends to a genuinely concave `ω̄ = ĝ` on `B̄` agreeing with `ω` on `B`.

The statement is the standard fact that an infimum of affine functions is concave, since each
`b ↦ ⟨p, b⟩ − g°(p)` is affine in `b` and the concavity inequality is preserved under infima:
for `a + b = 1` with `a, b ≥ 0`,
$$a \cdot ĝ(x) + b \cdot ĝ(y) \le \inf_p \big(a\cdot(\langle p, x\rangle - g^\circ(p)) + b \cdot (\langle p, y\rangle - g^\circ(p))\big) = ĝ(a\cdot x + b\cdot y),$$
using `a ≥ 0` and `b ≥ 0` to pull the infimum through the weighted sums. No exchange property is assumed;
this is a property of the construction for every `g`. -/
theorem concaveClosure_concaveOn {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) :
    ConcaveOn ℝ (hull B) (concaveClosure B g) := by sorry

end SteinitzExchange.Extension
