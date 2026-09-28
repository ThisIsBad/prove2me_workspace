import Mathlib

namespace TSPHeuristics.Shared

/-- A traveling salesman graph on the nodes `Fin n` (Rosenkrantz–Stearns–Lewis 1977, §1, p. 563):
the distance `d` is symmetric, nonnegative and satisfies the triangle inequality.
The field `diag` (`d i i = 0`) is not in the paper; it is a normalization, since `d(i, i)` never
enters the length of a tour, a subtour or an insertion cost. -/
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

/-- The length of the closed tour visiting the entries of the list `T` in order and returning to
the first one: `d(T₀, T₁) + ⋯ + d(T_{m-2}, T_{m-1}) + d(T_{m-1}, T₀)`. A one-node list `[a]`
gets `d a a` (which is `0` under `IsTSPDist`, the paper's "tour without edges", p. 570), and a
two-node list `[a, b]` gets `d a b + d b a`, the two-node tour of p. 570. -/
def cycleLength {n : ℕ} (d : Fin n → Fin n → ℝ) (T : List (Fin n)) : ℝ :=
  (List.zipWith d T (T.rotate 1)).sum

end TSPHeuristics.Shared
