import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

/-- Appendix, proof of Theorem 1, final sentence (Popescu 2007, p. 110): with
`y = (x′Σx)^{-1/2} Σ^{1/2} x`, every `Z` satisfies
`x′(μ + Σ^{1/2} Z) = x′μ + (x′Σx)^{1/2} y′Z`. -/
theorem affine_image_projection {n : ℕ} (μ x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) (hq : 0 < x.ofLp ⬝ᵥ S *ᵥ x.ofLp)
    (Z : EuclideanSpace ℝ (Fin n)) :
    let y : EuclideanSpace ℝ (Fin n) :=
      (x.ofLp ⬝ᵥ S *ᵥ x.ofLp) ^ (-(1 / 2 : ℝ)) • toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x
    ⟪x, μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) Z⟫ =
      ⟪x, μ⟫ + (x.ofLp ⬝ᵥ S *ᵥ x.ofLp) ^ (1 / 2 : ℝ) * ⟪y, Z⟫ := by sorry

end RobustMeanCov.Projection
