import Mathlib
import Definitions.Def_TamingMonster_CoordDescent_Setting
import Definitions.Def_TamingMonster_CoordDescent_Algorithm
import Definitions.Def_TamingMonster_CoordDescent_Potential

namespace TamingMonster.CoordDescent

/-- Lemma 6 (p. 10; proof App. D.2): let `Q` be a (nonnegative) weight vector with
`∑_π Q(π)(2K + b_π) > 2K`, and let `c = 2K / ∑_π Q(π)(2K + b_π)` as in Eq. (4). Then
`Φ(cQ) ≤ Φ(Q)`. -/
theorem potential_rescale_le {X : Type*} {K t : ℕ} (hK : 0 < K) (ht : 0 < t)
    (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) (H : History X K t)
    (μ : ℝ) (hμ : 0 < μ) (hμK : μ ≤ 1 / (2 * (K : ℝ)))
    (Q : Pi → ℝ) (hQ : ∀ π, 0 ≤ Q π)
    (hmass : 2 * (K : ℝ) < weightedMass Pi H μ Q) :
    potential Pi H μ (fun π => scaleFactor Pi H μ Q * Q π) ≤ potential Pi H μ Q := by sorry

end TamingMonster.CoordDescent

