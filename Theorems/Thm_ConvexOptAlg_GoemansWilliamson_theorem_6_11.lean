import Mathlib
import Definitions.Def_ConvexOptAlg_GoemansWilliamson_Defs

namespace ConvexOptAlg.GoemansWilliamson

open MeasureTheory ProbabilityTheory Matrix

/-- **Theorem 6.11** (Goemans–Williamson; Bubeck, arXiv:1405.4980v2, §6.6, p. 345). Let
`A ∈ ℝ₊ⁿˣⁿ` be a symmetric matrix of non-negative weights and `L = D − A` its graph Laplacian.
Let `Σ` be the solution to the SDP relaxation of MAXCUT. Let `ξ ∼ N(0, Σ)` and
`ζ = sign(ξ) ∈ {−1, 1}ⁿ`. Then `E ζ⊤Lζ ≥ 0.878 max_{x ∈ {−1,1}ⁿ} x⊤Lx`.

`Σ` is any maximizer of `⟨L, X⟩` over `X ∈ S₊ⁿ` with unit diagonal; `N(0, Σ)` is Mathlib's
`multivariateGaussian 0 Σ` (well defined for singular `Σ`). The integrand is bounded and
measurable; its integrability is asserted as part of the conclusion. -/
theorem theorem_6_11 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hsymm : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hopt : IsSDPRelaxationOptimum (laplacian A) Sig) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin n) => sgnVec ξ ⬝ᵥ laplacian A *ᵥ sgnVec ξ)
        (multivariateGaussian 0 Sig) ∧
      ∫ ξ, sgnVec ξ ⬝ᵥ laplacian A *ᵥ sgnVec ξ ∂(multivariateGaussian 0 Sig) ≥
        (0.878 : ℝ) * hypercubeMax (laplacian A) := by sorry

end ConvexOptAlg.GoemansWilliamson

