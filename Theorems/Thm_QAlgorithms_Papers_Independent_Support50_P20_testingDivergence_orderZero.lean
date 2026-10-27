import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P20

noncomputable section

open Filter

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P20

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace State)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.2, paragraph after (1): zero-error testing divergence equals
order-zero Renyi divergence, including orthogonal supports and infinity. -/
theorem testingDivergence_orderZero {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : State b) :
    hilbertTestingDivergence b 0 rho.val.val sigma.val.val =
      orderZeroDivergence b rho.val.val sigma.val.val := by sorry

end QAlgorithms.Papers.Independent.Support50.P20

end

