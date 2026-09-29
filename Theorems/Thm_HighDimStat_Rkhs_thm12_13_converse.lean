import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 12.13 (p. 391): given any Hilbert space `H` of real-valued functions on `X`
(embedded via the injective linear map `toFun`, Definition 12.12's "Hilbert space of
functions") in which the evaluation functionals are all bounded, there is a unique PSD
kernel `K` that satisfies the reproducing property (12.3) for `H`, via some feature map. -/
theorem thm12_13_converse (toFun : H →ₗ[ℝ] (X → ℝ)) (htoFun : Function.Injective toFun)
    (hEval : HasBoundedEvalFunctionals toFun) :
    ∃! K : X → X → ℝ, IsPSDKernel K ∧ ∃ feature : X → H, IsRKHS K toFun feature := by sorry

end HighDimStat.Rkhs
