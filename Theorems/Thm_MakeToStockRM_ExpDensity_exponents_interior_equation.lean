import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_generator
import Definitions.Def_MakeToStockRM_ExpDensity_expDensity

namespace MakeToStockRM.ExpDensity

theorem exponents_interior_equation (θ σ δ ϱ : ℝ) (hσ : 0 < σ) (hδ : 0 < δ) (hϱ : |ϱ| < 1) :
    ∀ z : ℝ × ℝ, adjointGenerator θ σ δ ϱ (expDensity θ σ δ ϱ) z = 0 := by sorry

end MakeToStockRM.ExpDensity
