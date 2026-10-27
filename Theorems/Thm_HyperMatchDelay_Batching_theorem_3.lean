import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace HyperMatchDelay.Batching

/-- Theorem 3, p. 7 (competitive clause; proof Appendix B.3, pp. 17–20): Randomized-Batching
using Depth-k Greedy as a subroutine is `1/d`-competitive for Online-(k, d)-Max-Matching.
For every shift `z < d` the output `M_z` is a matching of `E` whose every edge lies inside one
window (online feasibility), and its expected weight over a uniform shift
`Z ∈ {0, …, d - 1}` is at least `w(M̃)/d` for every matching `M̃` of `E`. -/
theorem theorem_3 (n d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (E : Finset (Finset ℕ))
    (w : Finset ℕ → ℝ) (hE : IsShareability n d k E w)
    (σ : Finset (Finset ℕ) → List (Finset ℕ)) (hσ : IsSortedOrder w σ) :
    (∀ z < d, IsMatching E (randomizedBatching σ w n d k E z) ∧
      ∀ e ∈ randomizedBatching σ w n d k E z, ∃ i ∈ batchIndices n d, e ⊆ window n d z i) ∧
    ∀ Mt : Finset (Finset ℕ), IsMatching E Mt →
      weight w Mt / d ≤
        (1 / (d : ℝ)) * ∑ z ∈ Finset.range d,
          weight w (randomizedBatching σ w n d k E z) := by sorry

end HyperMatchDelay.Batching

