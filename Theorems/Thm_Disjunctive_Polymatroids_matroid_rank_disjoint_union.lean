import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic

namespace Disjunctive.Polymatroids

/-- Proposition 13.16 (Balas §13.4, p. 224-225): for set functions `r₁,r₂` satisfying conditions
1-3 of Application 1, `conv(Z(r₁,r₂)) = {(x,y) : (|A|-x(A))/(|A|-r₁(A)) + (|B|-y(B))/(|B|-r₂(B))
≥1 for all A⊆M, B⊆N with r₁(A)<|A|, r₂(B)<|B|}`. -/
theorem matroid_rank_disjoint_union {m n : ℕ} (r1 : Finset (Fin m) → ℝ)
    (r2 : Finset (Fin n) → ℝ) (hr1 : IsApp1SetFunction r1) (hr2 : IsApp1SetFunction r2) :
    convexHull ℝ (ZDisjoint r1 r2) =
      {p : (Fin m → ℝ) × (Fin n → ℝ) | (∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ 1) ∧
        (∀ j, 0 ≤ p.2 j ∧ p.2 j ≤ 1) ∧
        ∀ A : Finset (Fin m), ∀ B : Finset (Fin n), r1 A < A.card → r2 B < B.card →
          1 ≤ ((A.card : ℝ) - SumOver p.1 A) / ((A.card : ℝ) - r1 A) +
            ((B.card : ℝ) - SumOver p.2 B) / ((B.card : ℝ) - r2 B)} := by sorry

end Disjunctive.Polymatroids

