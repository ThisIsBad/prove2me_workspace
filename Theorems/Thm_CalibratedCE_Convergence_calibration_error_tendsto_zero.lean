import Mathlib
import Definitions.Def_CalibratedCE_Shared_Calibration

open Filter Topology

namespace CalibratedCE.Convergence

/-- Proof of Theorem 1, p. 45: if player 1's forecasts are calibrated against player 2's plays,
the calibration error term of the decomposition display tends to `0`. -/
theorem calibration_error_tendsto_zero {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m)
    (f₁ : ℕ → Fin n → ℝ) (y : ℕ → Fin n) (hcal : Shared.Calibrated f₁ y) (a : Fin m) (b : Fin n) :
    Tendsto (fun t : ℕ => (t : ℝ)⁻¹ *
        ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          (Shared.rho f₁ y p b t - p b) * (Shared.N f₁ p t : ℝ)) atTop (𝓝 0) := by sorry

end CalibratedCE.Convergence
