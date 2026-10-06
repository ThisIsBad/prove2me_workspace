import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR

/-- Theorem 1 (Minty 1962): a monotone operator `T` on a Hilbert space is maximal iff
`im(I + T) = H`. -/
theorem minty_theorem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMonotoneOp T) :
    IsMaximalMonotone T ↔ imOp (opAdd opId T) = Set.univ := by sorry

end DouglasRachfordPPA.GenDR

