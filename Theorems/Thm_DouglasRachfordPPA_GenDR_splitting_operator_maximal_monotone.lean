import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_DouglasRachfordPPA_GenDR_SplittingOperator

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR
/-- Theorem 4: for `lam > 0`, if `A` and `B` are monotone then the splitting operator
`S_{lam,A,B}` is monotone; if `A` and `B` are maximal monotone, so is `S_{lam,A,B}`. -/
theorem splitting_operator_maximal_monotone {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (lam : ℝ) (hlam : 0 < lam) (A B : H → Set H) :
    (IsMonotoneOp A → IsMonotoneOp B → IsMonotoneOp (splittingOp lam A B)) ∧
    (IsMaximalMonotone A → IsMaximalMonotone B →
      IsMaximalMonotone (splittingOp lam A B)) := by sorry

end DouglasRachfordPPA.GenDR

