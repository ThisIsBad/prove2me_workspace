import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace HyperMatchDelay.Batching

/-- Lemma 4, p. 14 (competitive clause): on a rank-`k` hypergraph with non-negative weights,
Greedy (Algorithm 5, with any weight-sorted order) returns a matching whose weight is at least
`1/k` times the weight of every matching. -/
theorem lemma_4 (k : ℕ) (hk : 1 ≤ k) (w : Finset ℕ → ℝ)
    (σ : Finset (Finset ℕ) → List (Finset ℕ)) (hσ : IsSortedOrder w σ)
    (S : Finset (Finset ℕ)) (hS : ∀ e ∈ S, e.card ≤ k ∧ 0 ≤ w e) :
    IsMatching S (greedy σ S) ∧
    ∀ M, IsMatching S M → (1 / (k : ℝ)) * weight w M ≤ weight w (greedy σ S) := by sorry

end HyperMatchDelay.Batching

