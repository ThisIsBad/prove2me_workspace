import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_generator
import Definitions.Def_MakeToStockRM_ExpDensity_covMatrix
import Definitions.Def_MakeToStockRM_ExpDensity_expDensity

namespace MakeToStockRM.ExpDensity

open Matrix

theorem exponents_zero_flux (θ σ δ ϱ : ℝ) (hσ : 0 < σ) (hδ : 0 < δ) (hϱ : |ϱ| < 1) :
    ∀ z : ℝ × ℝ,
      (1 / 2 : ℝ) • (covMatrix σ δ ϱ *ᵥ
          ![partialX (expDensity θ σ δ ϱ) z, partialY (expDensity θ σ δ ϱ) z])
        = ![θ * expDensity θ σ δ ϱ z, 0] := by sorry

end MakeToStockRM.ExpDensity
