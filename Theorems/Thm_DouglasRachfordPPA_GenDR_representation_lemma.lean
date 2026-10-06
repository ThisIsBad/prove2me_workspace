import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR

/-- Corollary 2.3 (Representation Lemma): for `c > 0` and monotone `T`, every `z` can be
written in at most one way as `x + c y` with `y ∈ T x`; if `T` is maximal, in exactly one way. -/
theorem representation_lemma {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (c : ℝ) (hc : 0 < c) (T : H → Set H) (hT : IsMonotoneOp T) :
    (∀ z x y x' y' : H, y ∈ T x → y' ∈ T x' → z = x + c • y → z = x' + c • y' →
      x = x' ∧ y = y') ∧
    (IsMaximalMonotone T → ∀ z : H, ∃! p : H × H, p.2 ∈ T p.1 ∧ z = p.1 + c • p.2) := by sorry

end DouglasRachfordPPA.GenDR

