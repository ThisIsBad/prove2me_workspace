import Mathlib

namespace TSPHeuristics.NNLower

/-- A traveling salesman graph on the nodes `Fin n` (Rosenkrantz–Stearns–Lewis 1977, §1, p. 563):
the distance `d` is symmetric, nonnegative and satisfies the triangle inequality.
The field `diag` (`d i i = 0`) is not in the paper; it is a normalization, since a distance
`d(i, i)` never enters the length of a tour. -/
structure IsTSPDist {n : ℕ} (d : Fin n → Fin n → ℝ) : Prop where
  symm : ∀ i j, d i j = d j i
  nonneg : ∀ i j, 0 ≤ d i j
  triangle : ∀ i j k, d i k ≤ d i j + d j k
  diag : ∀ i, d i i = 0

/-- The length of the tour that visits `τ 0, τ 1, …, τ (n - 1)` in this order and returns to
`τ 0`: the sum of the lengths of its `n` edges. -/
def tourLength {n : ℕ} (d : Fin n → Fin n → ℝ) (τ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ k, d (τ k) (τ (finRotate n k))

/-- OPTIMAL: the minimal length of a tour, the minimum over all orderings of the nodes (a
nonempty finite set). -/
def optimal {n : ℕ} (d : Fin n → Fin n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (tourLength d)

/-- `τ` is a tour the nearest neighbor algorithm (p. 564) can produce: starting from `τ 0`, each
step goes from the node `τ k` last added to a node `τ (k + 1)` that is at least as close to `τ k`
as every node not yet on the path. The start node and the resolution of ties are arbitrary. -/
def IsNearestNeighborTour {n : ℕ} (d : Fin n → Fin n → ℝ) (τ : Equiv.Perm (Fin n)) : Prop :=
  ∀ k j : Fin n, k.val + 1 < n → (∀ l, l ≤ k → τ l ≠ j) →
    d (τ k) (τ (finRotate n k)) ≤ d (τ k) j

end TSPHeuristics.NNLower
