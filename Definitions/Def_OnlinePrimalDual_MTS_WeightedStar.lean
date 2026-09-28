import Mathlib

namespace OnlinePrimalDual.MTS

/-- Buchbinder & Naor, *The Design of Competitive Online Algorithms via a Primal-Dual Approach*,
FnT TCS 2009, Section 6, p. 142-144 (PDF p. 53-55). The weighted-star metric: `V` is the (finite,
in the book, though finiteness is not needed for this mission's two lemmas) set of leaves
`{1,…,N}`, `centerDist i` is the distance `d′(i)` from leaf `i` to the star's center. The book
immediately collapses this to a single per-state charge `d(i) := 2d′(i)` (p. 143: "We are going
to charge the algorithm by `2d′(i)` whenever the server moves from state `i` to another state...
From now on we only use `d(i) = 2d′(i)` to denote the cost of moving from state `i` to any other
state"), exploiting the star's structure (any transition `i → j` costs at most `d′(i) + d′(j)`
via the center, so charging the doubled *source* distance alone, independent of the destination,
upper-bounds every transition without needing the full metric `d : V × V → ℝ`). This is exactly
the quantity Lemma 6.1 and Lemma 6.2 operate on, via `WeightedStar.d` below. -/
structure WeightedStar (V : Type*) where
  /-- `d′(i)`, the distance from leaf `i` to the star's center. -/
  centerDist : V → ℝ
  hcenterDist_nonneg : ∀ v, 0 ≤ centerDist v

end OnlinePrimalDual.MTS
