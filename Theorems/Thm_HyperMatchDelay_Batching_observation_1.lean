import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace HyperMatchDelay.Batching

/-- Observation 1, p. 6: every hyperedge `e` of a shareability hypergraph lies in `E_z` for at
least `d - diam(e)` of the `d` shifts `z ∈ {0, …, d - 1}`. -/
theorem observation_1 (n d k : ℕ) (hd : 1 ≤ d) (E : Finset (Finset ℕ))
    (w : Finset ℕ → ℝ) (hE : IsShareability n d k E w) (e : Finset ℕ) (he : e ∈ E) :
    d - diam e ≤ ((Finset.range d).filter (fun z => e ∈ shiftEdges E n d z)).card := by sorry

end HyperMatchDelay.Batching

