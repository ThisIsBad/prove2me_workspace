import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_expDensity
import Definitions.Def_MakeToStockRM_ExpDensity_region

namespace MakeToStockRM.ExpDensity

theorem normalizing_constant_exists (θ σ δ ϱ ymin ymax : ℝ) (η ξ : ℝ → ℝ)
    (hy : ymin < ymax) (hη : Continuous η) (hξ : Continuous ξ)
    (hlt : ∀ y ∈ Set.Icc ymin ymax, η y < ξ y) :
    MeasureTheory.IntegrableOn (expDensity θ σ δ ϱ) (region η ξ ymin ymax) ∧
      ∃! K : ℝ, 0 < K ∧ ∫ z in region η ξ ymin ymax, K * expDensity θ σ δ ϱ z = 1 := by sorry

end MakeToStockRM.ExpDensity
