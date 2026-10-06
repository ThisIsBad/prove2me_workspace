import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR

/-- Theorem 2: for `c > 0`, `T` is monotone iff its resolvent `J_{cT} = (I + cT)⁻¹` is firmly
nonexpansive, and `T` is maximal monotone iff `J_{cT}` is firmly nonexpansive with
`dom J_{cT} = H`. -/
theorem resolvent_firmly_nonexpansive_iff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (c : ℝ) (hc : 0 < c) (T : H → Set H) :
    (IsMonotoneOp T ↔ IsFirmlyNonexpansiveOp (opResolvent c T)) ∧
    (IsMaximalMonotone T ↔
      IsFirmlyNonexpansiveOp (opResolvent c T) ∧ dom (opResolvent c T) = Set.univ) := by sorry

end DouglasRachfordPPA.GenDR

