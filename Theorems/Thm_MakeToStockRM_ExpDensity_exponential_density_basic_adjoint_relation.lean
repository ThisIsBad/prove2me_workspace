import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_generator
import Definitions.Def_MakeToStockRM_ExpDensity_covMatrix
import Definitions.Def_MakeToStockRM_ExpDensity_expDensity
import Definitions.Def_MakeToStockRM_ExpDensity_region
import Definitions.Def_MakeToStockRM_ExpDensity_boundaryTerm

namespace MakeToStockRM.ExpDensity

theorem exponential_density_basic_adjoint_relation (θ σ δ ϱ ymin ymax : ℝ) (η ξ : ℝ → ℝ)
    (f : ℝ × ℝ → ℝ) (hσ : 0 < σ) (hδ : 0 < δ) (hϱ : |ϱ| < 1) (hy : ymin < ymax)
    (hη : ContDiff ℝ 1 η) (hξ : ContDiff ℝ 1 ξ) (hlt : ∀ y ∈ Set.Icc ymin ymax, η y < ξ y)
    (hf : ContDiff ℝ 2 f) :
    (∫ z in region η ξ ymin ymax, generator θ σ δ ϱ f z * expDensity θ σ δ ϱ z)
      + 1 / 2 * boundaryTerm σ δ ϱ η ξ ymin ymax f (expDensity θ σ δ ϱ) = 0 := by sorry

end MakeToStockRM.ExpDensity

