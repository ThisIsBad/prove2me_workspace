import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

/-- Appendix, proof of Theorem 1 (Popescu 2007, p. 109): for `Σ ⪰ 0` and `x′Σx > 0`, the vector
`y = (x′Σx)^{-1/2} Σ^{1/2} x` satisfies `y′y = 1`. -/
theorem normalized_direction_inner_self {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) (hq : 0 < x.ofLp ⬝ᵥ S *ᵥ x.ofLp) :
    let y : EuclideanSpace ℝ (Fin n) :=
      (x.ofLp ⬝ᵥ S *ᵥ x.ofLp) ^ (-(1 / 2 : ℝ)) • toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x
    ⟪y, y⟫ = 1 := by sorry

end RobustMeanCov.Projection
