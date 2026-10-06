import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_DouglasRachfordPPA_GenDR_SplittingOperator

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR
/-- Corollary 4.1: for `lam > 0` and maximal monotone `A`, `B`, the resolvent
`(I + S_{lam,A,B})⁻¹` of the splitting operator is firmly nonexpansive and has full domain. -/
theorem splitting_resolvent_firmly_nonexpansive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (lam : ℝ) (hlam : 0 < lam) (A B : H → Set H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B) :
    IsFirmlyNonexpansiveOp (opResolvent 1 (splittingOp lam A B)) ∧
    dom (opResolvent 1 (splittingOp lam A B)) = Set.univ := by sorry

end DouglasRachfordPPA.GenDR

