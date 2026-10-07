import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix

namespace BoydADMM.ModelFit

/-- §8.2.1, p. 65: the distributed-lasso `xᵢ`-update is a ridge regression with the unique
solution `xᵢ = (AᵢᵀAᵢ + ρI)⁻¹(Aᵢᵀbᵢ + ρ(z − uᵢ))`. -/
theorem lasso_x_update_ridge {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (z u : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hρ : 0 < ρ)
    (x : EuclideanSpace ℝ (Fin n)) :
    IsMinOn (fun x' : EuclideanSpace ℝ (Fin n) =>
        1 / 2 * ‖Matrix.toEuclideanLin A x' - b‖ ^ 2 + ρ / 2 * ‖x' - z + u‖ ^ 2) Set.univ x ↔
      x = Matrix.toEuclideanLin ((Aᵀ * A + ρ • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹)
        (Matrix.toEuclideanLin Aᵀ b + ρ • (z - u)) := by sorry

end BoydADMM.ModelFit

