import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem component_separable {n p : ℕ} (f : Fin n → ℝ → ℝ) (A : Matrix (Fin p) (Fin n) ℝ)
    (d : Fin n → ℝ) (hdiag : Aᵀ * A = Matrix.diagonal d) (ρ : ℝ) (hρ : 0 < ρ)
    (v : EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin n)) :
    IsXUpdate Set.univ (fun y => ∑ i, f i (y i)) ρ A v x ↔
      ∀ i, ∀ t : ℝ,
        f i (x i) + (ρ / 2) * (d i * x i ^ 2 - 2 * (Matrix.toEuclideanLin Aᵀ v) i * x i) ≤
          f i t + (ρ / 2) * (d i * t ^ 2 - 2 * (Matrix.toEuclideanLin Aᵀ v) i * t) := by sorry

end BoydADMM.Prox

