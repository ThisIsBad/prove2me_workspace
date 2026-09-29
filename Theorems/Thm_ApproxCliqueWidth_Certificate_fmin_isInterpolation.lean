import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_Interpolation

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour Proposition 4.2 (p. 519). -/
theorem fmin_isInterpolation {V : Type*} [Fintype V] [DecidableEq V]
    (f : Finset V → ℤ) (hsub : IsSubmodular f) (hmin : ∀ X : Finset V, f ∅ ≤ f X) :
    IsInterpolation f (fmin f) := by sorry

end ApproxCliqueWidth.Certificate
