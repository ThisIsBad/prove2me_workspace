import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

/-- Appendix, proof of Theorem 1, final sentence (Popescu 2007, p. 110): if `Z ∼ (0, Iₙ)` and
`Σ ⪰ 0`, then `R = μ + Σ^{1/2} Z ∼ (μ, Σ)`. -/
theorem affine_image_mem {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef)
    (Q : Measure (EuclideanSpace ℝ (Fin n)))
    (hQ : Q ∈ MeanCovClass (0 : EuclideanSpace ℝ (Fin n)) (1 : Matrix (Fin n) (Fin n) ℝ)) :
    Q.map (fun Z => μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) Z) ∈ MeanCovClass μ S := by sorry

end RobustMeanCov.Projection
