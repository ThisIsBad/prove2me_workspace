import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem quadratic_affine_kkt {n m : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (q : EuclideanSpace ℝ (Fin n)) (r : ℝ) (F : Matrix (Fin m) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin m)) (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ (z u x : EuclideanSpace ℝ (Fin n)),
        IsProx (affineSet F g) (quadObj P q r) ρ (z - u) x ↔
          ∃ ν : EuclideanSpace ℝ (Fin m),
            Matrix.toEuclideanLin (P + ρ • (1 : Matrix (Fin n) (Fin n) ℝ)) x
                + Matrix.toEuclideanLin Fᵀ ν + (q - ρ • (z - u)) = 0 ∧
              Matrix.toEuclideanLin F x - g = 0) ∧
      ((affineSet F g).Nonempty →
        ∃ (M : Matrix (Fin n) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin n)),
          ∀ (v x : EuclideanSpace ℝ (Fin n)),
            IsProx (affineSet F g) (quadObj P q r) ρ v x ↔
              x = Matrix.toEuclideanLin M v + b) := by sorry

end BoydADMM.Prox

