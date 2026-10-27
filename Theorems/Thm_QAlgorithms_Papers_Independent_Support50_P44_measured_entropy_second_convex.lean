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

/-- PDF p.25, Lemma B.4, (155): convexity in the second input, without orthogonality. -/
theorem measured_entropy_second_convex {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (rho sigma sigma2 : H →L[ℂ] H)
    (hrho : IsHilbertDensity b rho) (hsigma : IsHilbertDensity b sigma)
    (hsigma2 : IsHilbertDensity b sigma2) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    measuredRelativeEntropy b rho (hilbertMix p sigma sigma2) ≤
      ENNReal.ofReal p * measuredRelativeEntropy b rho sigma +
        ENNReal.ofReal (1-p) * measuredRelativeEntropy b rho sigma2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P44

end

