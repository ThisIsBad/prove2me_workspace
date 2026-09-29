import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **§1.4.2, display (1)**, Arrow & Debreu, Econometrica 22 (1954), p. 272 (PDF p. 9): each
individual spends his entire potential income — if Condition 2 holds at `(p^*, x^*, y^*)`, then
for every consumer `i`,
`p^*·x_i^* = p^*·ζ_i + Σ_j α_{ij} p^*·y_j^*`.

**Formalization Note.** The paragraph uses Condition 2, III.b, III.c and the convexity of `X_i`
(the point `t x_i' + (1 − t) x_i^*` must lie in `X_i`); Assumption II supplies the convexity.
Nothing is assumed about `p^*` (not even Condition 3): the argument does not use it. -/
theorem budget_exhausted {l m n : ℕ} (E : Economy l m n) (hII : AssumptionII E)
    (hIIIb : AssumptionIIIb E) (hIIIc : AssumptionIIIc E)
    (p : Fin l → ℝ) (x : Fin m → Fin l → ℝ) (y : Fin n → Fin l → ℝ)
    (h2 : Condition2 E p x y) :
    ∀ i, p ⬝ᵥ x i = income E p y i := by sorry

end ArrowDebreu.ThmI
