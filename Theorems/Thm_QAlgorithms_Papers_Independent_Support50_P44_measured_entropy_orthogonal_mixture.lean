import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P44

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass compression)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Renew46.P37 (classicalKL)

open Filter

open scoped ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF pp.24–25, Lemma B.3, (149): affinity of the finite-POVM supremum.
There is no added optimal-measurement hypothesis. -/
theorem measured_entropy_orthogonal_mixture {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (rho rho2 sigma sigma2 : H →L[ℂ] H)
    (hrho : IsHilbertDensity b rho) (hrho2 : IsHilbertDensity b rho2)
    (hsigma : IsHilbertDensity b sigma) (hsigma2 : IsHilbertDensity b sigma2)
    (horth : OrthogonalBlocks rho rho2 sigma sigma2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    measuredRelativeEntropy b (hilbertMix p rho rho2) (hilbertMix p sigma sigma2) =
      ENNReal.ofReal p * measuredRelativeEntropy b rho sigma +
        ENNReal.ofReal (1-p) * measuredRelativeEntropy b rho2 sigma2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P44

end

