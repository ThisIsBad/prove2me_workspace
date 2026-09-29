import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_Interpolation
import Definitions.Def_ApproxCliqueWidth_Certificate_CutRank

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour Section 6, p. 522, the claim after Definition 6.1: `cutrk_G` is symmetric and
submodular, `∅` minimizes it (the standing assumption of Definition 4.1), and `cutrk*_G` is an
interpolation of `cutrk_G`. -/
theorem cutrk_symmetric_interpolation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsSymmetric (cutrk G) ∧ IsSubmodular (cutrk G) ∧
      (∀ X : Finset V, cutrk G ∅ ≤ cutrk G X) ∧ IsInterpolation (cutrk G) (cutrkStar G) := by sorry

end ApproxCliqueWidth.Certificate
