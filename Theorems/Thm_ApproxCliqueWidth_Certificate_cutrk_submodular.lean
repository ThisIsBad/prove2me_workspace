import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_CutRank

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour Corollary 6.2 (p. 522): submodularity of `cutrk*_G` on disjoint pairs and of
`cutrk_G`. -/
theorem cutrk_submodular {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∀ X₁ Y₁ X₂ Y₂ : Finset V, Disjoint X₁ Y₁ → Disjoint X₂ Y₂ →
        cutrkStar G (X₁ ∩ X₂) (Y₁ ∪ Y₂) + cutrkStar G (X₁ ∪ X₂) (Y₁ ∩ Y₂) ≤
          cutrkStar G X₁ Y₁ + cutrkStar G X₂ Y₂) ∧
    IsSubmodular (cutrk G) := by sorry

end ApproxCliqueWidth.Certificate
