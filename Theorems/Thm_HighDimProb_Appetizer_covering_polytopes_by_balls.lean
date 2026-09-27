import Mathlib

namespace HighDimProb.Appetizer

/-- **Corollary 0.0.4** (Covering polytopes by balls), Vershynin,
*High-Dimensional Probability* (2018), p. 3.

Let `P` be a polytope in `ℝⁿ` with `N` vertices and whose diameter is bounded
by `1`; identify `P` with the convex hull of its finite vertex set `T`
(`#T = N`), exactly as the book's own proof does. Then `P` can be covered by
at most `N ^ ⌈1/ε²⌉` Euclidean balls of radius `ε > 0`. -/
theorem covering_polytopes_by_balls {n N : ℕ} (T : Finset (EuclideanSpace ℝ (Fin n)))
    (hTcard : T.card = N) (hTdiam : Metric.diam (T : Set (EuclideanSpace ℝ (Fin n))) ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ centers : Finset (EuclideanSpace ℝ (Fin n)),
      centers.card ≤ N ^ ⌈(1 : ℝ) / ε ^ 2⌉₊ ∧
      convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin n))) ⊆
        ⋃ c ∈ centers, Metric.closedBall c ε := by sorry

end HighDimProb.Appetizer
