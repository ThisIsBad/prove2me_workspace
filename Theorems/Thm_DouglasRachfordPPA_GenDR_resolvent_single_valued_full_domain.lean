import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR

/-- Corollary 2.2: for `c > 0` the resolvent `J_{cT}` of a monotone operator is single-valued;
if `T` is maximal monotone it has full domain. The third conjunct restates the maximal case as
existence and uniqueness of a resolvent function `J : H → H`. -/
theorem resolvent_single_valued_full_domain {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (c : ℝ) (hc : 0 < c) (T : H → Set H) :
    (IsMonotoneOp T → IsSingleValuedOp (opResolvent c T)) ∧
    (IsMaximalMonotone T → dom (opResolvent c T) = Set.univ) ∧
    (IsMaximalMonotone T → ∃! J : H → H, IsResolvent c T J) := by sorry

end DouglasRachfordPPA.GenDR

