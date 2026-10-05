import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic

namespace Disjunctive.Polymatroids

/-- Corollary 13.21 (Balas §13.7, p. 231): for `r₁,r₂` satisfying conditions 1-3 of Application 1,
`conv(P(r₁)∪P(r₂)) = {w∈[0,1]ⁿ : w=x+y, (|A|-x(A))/(|A|-r₁(A)) + (|B|-y(B))/(|B|-r₂(B)) ≥1 for
all A,B⊆N with r₁(A)<|A|, r₂(B)<|B|}`. -/
theorem polymatroid_union_lifted {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ)
    (hr1 : IsApp1SetFunction r1) (hr2 : IsApp1SetFunction r2) :
    convexHull ℝ (PolymatroidP r1 ∪ PolymatroidP r2) =
      {w : Fin n → ℝ | (∀ i, 0 ≤ w i ∧ w i ≤ 1) ∧
        ∃ x y : Fin n → ℝ, w = x + y ∧
          ∀ A B : Finset (Fin n), r1 A < A.card → r2 B < B.card →
            1 ≤ ((A.card : ℝ) - SumOver x A) / ((A.card : ℝ) - r1 A) +
              ((B.card : ℝ) - SumOver y B) / ((B.card : ℝ) - r2 B)} := by sorry

end Disjunctive.Polymatroids

