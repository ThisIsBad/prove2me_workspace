import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic

namespace Disjunctive.Polymatroids

/-- Theorem 13.24 (Balas §13.8, p. 232), the goal theorem of this mission and the book's closing
result: for polymatroid rank functions `r₁,r₂`, `conv(P(r₁)∪P(r₂))` has a closed-form description
in the original variable space: `x(A)≤max{r₁(A),r₂(A)}` for every `A⊆N`, together with a two-set
inequality for every pair `A,B⊆N` with `(r₁(A)-r₂(A))(r₁(B)-r₂(B))<0`. -/
theorem polymatroid_union_closed_form {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ)
    (hr1 : IsPolymatroidRankFunction r1) (hr2 : IsPolymatroidRankFunction r2) :
    convexHull ℝ (PolymatroidP r1 ∪ PolymatroidP r2) =
      {x : Fin n → ℝ | 0 ≤ x ∧ (∀ A : Finset (Fin n), SumOver x A ≤ max (r1 A) (r2 A)) ∧
        ∀ A B : Finset (Fin n), (r1 A - r2 A) * (r1 B - r2 B) < 0 →
          (r2 B - r1 B) / (r1 A * r2 B - r1 B * r2 A) * SumOver x A +
            (r1 A - r2 A) / (r1 A * r2 B - r1 B * r2 A) * SumOver x B ≤ 1} := by sorry

end Disjunctive.Polymatroids

