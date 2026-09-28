import Mathlib

namespace LogRegretOCO.FTAL
theorem elliptical_potential {n : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin n)) (r ε : ℝ) (T : ℕ)
    (hr : 0 < r) (hε : 0 < ε) (hu : ∀ t ∈ Finset.Icc 1 T, ‖u t‖ ≤ r) :
    let V : ℕ → Matrix (Fin n) (Fin n) ℝ := fun t =>
      ∑ τ ∈ Finset.Icc 1 t, Matrix.vecMulVec (WithLp.ofLp (u τ)) (WithLp.ofLp (u τ))
        + ε • (1 : Matrix (Fin n) (Fin n) ℝ)
    ∑ t ∈ Finset.Icc 1 T, dotProduct (WithLp.ofLp (u t)) (Matrix.mulVec (V t)⁻¹ (WithLp.ofLp (u t)))
      ≤ n * Real.log (r ^ 2 * T / ε + 1) := by sorry
end LogRegretOCO.FTAL

