import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem quadratic_xUpdate {n p : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (q : EuclideanSpace ℝ (Fin n)) (r : ℝ) (A : Matrix (Fin p) (Fin n) ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hinv : IsUnit (P + ρ • (Aᵀ * A))) :
    (P + ρ • (Aᵀ * A)).PosDef ∧
      ∀ (v : EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin n)),
        IsXUpdate Set.univ (quadObj P q r) ρ A v x ↔
          x = Matrix.toEuclideanLin (P + ρ • (Aᵀ * A))⁻¹
            (ρ • Matrix.toEuclideanLin Aᵀ v - q) := by sorry

end BoydADMM.Prox

