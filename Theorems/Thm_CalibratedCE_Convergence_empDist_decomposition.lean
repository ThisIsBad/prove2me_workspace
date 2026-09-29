import Mathlib
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_EmpDist

namespace CalibratedCE.Convergence

/-- Proof of Theorem 1, p. 45, the decomposition display: when player 1 plays `R₁ (f₁ s)` in
round `s`, the empirical frequency of `(a, b)` splits into a forecast-weighted main term and a
calibration error term. The sums run over the forecasts issued in the first `t` rounds at
which player 1 plays `a`. -/
theorem empDist_decomposition {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (f₁ : ℕ → Fin n → ℝ)
    (y : ℕ → Fin n) (t : ℕ) (a : Fin m) (b : Fin n) :
    empDist (fun s => R₁ (f₁ s)) y t a b =
        (t : ℝ)⁻¹ * ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          (((Finset.range t).filter (fun r => f₁ r = p ∧ y r = b)).card : ℝ) ∧
    empDist (fun s => R₁ (f₁ s)) y t a b =
        (t : ℝ)⁻¹ * ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          Shared.rho f₁ y p b t * (Shared.N f₁ p t : ℝ) ∧
    empDist (fun s => R₁ (f₁ s)) y t a b =
        (t : ℝ)⁻¹ * ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          p b * (Shared.N f₁ p t : ℝ) +
        (t : ℝ)⁻¹ * ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          (Shared.rho f₁ y p b t - p b) * (Shared.N f₁ p t : ℝ) := by sorry

end CalibratedCE.Convergence
