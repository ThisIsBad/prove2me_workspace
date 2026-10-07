import Mathlib
import Definitions.Def_ConvexOptAlg_GoemansWilliamson_Defs

namespace ConvexOptAlg.GoemansWilliamson

open MeasureTheory ProbabilityTheory

/-- **Lemma 6.12** (Bubeck, arXiv:1405.4980v2, §6.6, p. 345). Let `ξ ∼ N(0, Σ)` with `Σ i i = 1`
for `i ∈ [n]`, and `ζ = sign(ξ)`. Then `E ζᵢζⱼ = (2/π) arcsin(Σ i j)`.

`N(0, Σ)` is Mathlib's `multivariateGaussian 0 Σ` on `EuclideanSpace ℝ (Fin n)` (the centered
Gaussian with covariance matrix `Σ`, defined for every positive semidefinite `Σ`, singular or
not); `Σ` positive semidefinite is implicit in the book (it is a covariance matrix). The sign
takes values in `{−1, 1}` (`sgn 0 = 1`). The integrand is bounded and measurable; its
integrability is asserted as part of the conclusion. -/
theorem lemma_6_12 {n : ℕ} (Sig : Matrix (Fin n) (Fin n) ℝ) (hpsd : Sig.PosSemidef)
    (hdiag : ∀ i, Sig i i = 1) (i j : Fin n) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin n) => sgn (ξ i) * sgn (ξ j))
        (multivariateGaussian 0 Sig) ∧
      ∫ ξ, sgn (ξ i) * sgn (ξ j) ∂(multivariateGaussian 0 Sig) =
        2 / Real.pi * Real.arcsin (Sig i j) := by sorry

end ConvexOptAlg.GoemansWilliamson

