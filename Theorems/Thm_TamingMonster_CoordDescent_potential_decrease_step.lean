import Mathlib
import Definitions.Def_TamingMonster_CoordDescent_Setting
import Definitions.Def_TamingMonster_CoordDescent_Algorithm
import Definitions.Def_TamingMonster_CoordDescent_Potential

namespace TamingMonster.CoordDescent

/-- Lemma 7 (p. 10; proof App. D.3): let `Q` be a (nonnegative) set of weights and suppose that
`D_π(Q) > 0` for some policy `π`. Let `Q'` be the copy of `Q` with `Q'(π) = Q(π) + α`, where
`α = α_π(Q)`. Then `α > 0` and, with `τ = t` the length of the history,
`Φ(Q) − Φ(Q') ≥ τμ² / (4(1 − Kμ))` (Eq. (7)). -/
theorem potential_decrease_step {X : Type*} {K t : ℕ} (hK : 0 < K) (ht : 0 < t)
    (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) (H : History X K t)
    (μ : ℝ) (hμ : 0 < μ) (hμK : μ ≤ 1 / (2 * (K : ℝ)))
    (Q : Pi → ℝ) (hQ : ∀ π, 0 ≤ Q π) (π : Pi)
    (hD : 0 < Dfun Pi H μ Q π) :
    0 < alphaStep Pi H μ Q π ∧
      (t : ℝ) * μ ^ 2 / (4 * (1 - (K : ℝ) * μ))
        ≤ potential Pi H μ Q - potential Pi H μ (addAlpha Pi H μ Q π) := by sorry

end TamingMonster.CoordDescent

