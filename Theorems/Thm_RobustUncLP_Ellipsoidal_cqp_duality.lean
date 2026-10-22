import Mathlib
import Definitions.Def_RobustUncLP_Ellipsoidal_Setting
import Definitions.Def_RobustUncLP_Ellipsoidal_CQP

namespace RobustUncLP.Ellipsoidal

open Matrix CQPData

/-- Appendix, claim (II), p. 15 (conic quadratic duality, cited from Nesterov–Nemirovski 1994,
Theorem 4.2.1): if `(CQP_p)` is strictly feasible and its objective is bounded below on its
feasible set, then `(CQP_d)` is solvable and the two optimal values coincide. -/
theorem cqp_duality {N p k : ℕ} (P : CQPData N p k)
    (hstrict : ∃ z, P.R *ᵥ z = P.r ∧ ∀ ℓ, euclidNorm (P.A ℓ *ᵥ z - P.b ℓ) < P.c ℓ ⬝ᵥ z - P.d ℓ)
    (hbdd : BddBelow (P.primalObj '' P.primalFeas)) :
    ∃ v : ℝ, IsGLB (P.primalObj '' P.primalFeas) v ∧ IsGreatest (P.dualObj '' P.dualFeas) v := by sorry

end RobustUncLP.Ellipsoidal

