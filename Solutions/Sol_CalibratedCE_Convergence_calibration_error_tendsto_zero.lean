import Mathlib
import Definitions.Def_CalibratedCE_Shared_Calibration

open Filter Topology

namespace CalibratedCE.Convergence

theorem aux_cetz_bound {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m)
    (f₁ : ℕ → Fin n → ℝ) (y : ℕ → Fin n) (a : Fin m) (b : Fin n) (t : ℕ) :
    ‖(t : ℝ)⁻¹ *
        ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          (Shared.rho f₁ y p b t - p b) * (Shared.N f₁ p t : ℝ)‖ ≤
      Shared.calibScore f₁ y b t := by
  rw [Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast]
  unfold Shared.calibScore
  rw [← Finset.sum_div, div_eq_inv_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc |∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          (Shared.rho f₁ y p b t - p b) * (Shared.N f₁ p t : ℝ)|
        ≤ ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          |(Shared.rho f₁ y p b t - p b) * (Shared.N f₁ p t : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          |Shared.rho f₁ y p b t - p b| * (Shared.N f₁ p t : ℝ) := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [abs_mul, Nat.abs_cast]
    _ ≤ ∑ p ∈ (Finset.range t).image f₁,
          |Shared.rho f₁ y p b t - p b| * (Shared.N f₁ p t : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)

end CalibratedCE.Convergence

open CalibratedCE.Convergence
open CalibratedCE

theorem solution {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m)
    (f₁ : ℕ → Fin n → ℝ) (y : ℕ → Fin n) (hcal : Shared.Calibrated f₁ y) (a : Fin m) (b : Fin n) :
    Tendsto (fun t : ℕ => (t : ℝ)⁻¹ *
        ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
          (Shared.rho f₁ y p b t - p b) * (Shared.N f₁ p t : ℝ)) atTop (𝓝 0) :=
  squeeze_zero_norm (fun t => aux_cetz_bound R₁ f₁ y a b t) (hcal b)
