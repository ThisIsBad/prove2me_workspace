import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace HyperMatchDelay.Batching

/-- Appendix B.3, p. 19, display (a)–(c): Depth-k Greedy satisfies condition (3). For every
matching `M̃` of a shareability hypergraph, split into its long edges
`M̃_ℓ = {e : diam(e) > d - k}` and short edges `M̃_s = {e : diam(e) ≤ d - k}`, and every batch
`W_{z,i}`, `w(M_{z,i}) ≥ w(M̃_ℓ ∩ E_{z,i}) + (1/k) w(M̃_s ∩ E_{z,i})`. -/
theorem condition_3 (n d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (E : Finset (Finset ℕ))
    (w : Finset ℕ → ℝ) (hE : IsShareability n d k E w)
    (σ : Finset (Finset ℕ) → List (Finset ℕ)) (hσ : IsSortedOrder w σ)
    (Mt : Finset (Finset ℕ)) (hMt : IsMatching E Mt) (z : ℕ) (i : ℤ) :
    weight w (Mt.filter (fun e => (d : ℤ) - k < (diam e : ℤ)) ∩ batchEdges E n d z i) +
      (1 / (k : ℝ)) *
        weight w (Mt.filter (fun e => (diam e : ℤ) ≤ (d : ℤ) - k) ∩ batchEdges E n d z i) ≤
    weight w (depthKGreedy σ w k (window n d z i) (batchEdges E n d z i)) := by sorry

end HyperMatchDelay.Batching

