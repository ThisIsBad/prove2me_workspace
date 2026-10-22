import Mathlib
import Definitions.Def_RobustUncLP_Ellipsoidal_Setting
import Definitions.Def_RobustUncLP_Ellipsoidal_SystemC

namespace RobustUncLP.Ellipsoidal

open Matrix EllipsoidalData

/-- Appendix, p. 16: under conditions B and C, every problem `(P_i[x])` is strictly feasible and
its objective is bounded below on its feasible set. -/
theorem P_strictly_feasible_bddBelow {m n k : ℕ} (D : EllipsoidalData m n k)
    (hB : UncBounded D.uncSet) (hC : D.SlaterC) :
    (∃ u ∈ PFeas D, ∀ ℓ, euclidNorm (D.Q ℓ *ᵥ u ℓ) < 1) ∧
      ∀ (x : Fin n → ℝ) (i : Fin m),
        BddBelow ((fun u => (D.Pi 0 (u 0) *ᵥ x) i) '' PFeas D) := by sorry

end RobustUncLP.Ellipsoidal

