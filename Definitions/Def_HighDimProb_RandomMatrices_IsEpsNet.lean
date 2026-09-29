import Mathlib

namespace HighDimProb.RandomMatrices

/-- **Definition 4.2.1** (ε-net), Vershynin, *High-Dimensional Probability* (2018), p. 81.

Let `(T, d)` be a metric space, `K ⊆ T`, `ε > 0`. A subset `N ⊆ K` is an `ε`-net of `K` if
every point of `K` is within distance `ε` of some point of `N`. -/
def IsEpsNet {T : Type*} [PseudoMetricSpace T] (K : Set T) (N : Set T) (ε : ℝ) : Prop :=
  N ⊆ K ∧ ∀ x ∈ K, ∃ y ∈ N, dist x y ≤ ε

end HighDimProb.RandomMatrices
