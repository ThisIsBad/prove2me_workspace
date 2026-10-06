import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*, SIAM J.
Comput. 38 (2008), Theorem 2.1, proof, (2.1), p. 1607 (PDF p. 6): Rosenthal's function
`Φ(S) = Σ_{e∈E} Σ_{x=1}^{x_e} f_e(x)` is an exact potential — when a single player `i` deviates
from `S` to `S′ = (S₋ᵢ, T)`, the change of `Φ` equals the change of player `i`'s cost.

**Formalization Note.** Stated for every congestion game (arbitrary latencies `f_e`, arbitrary
strategy families) and every deviation, as on the page. -/
theorem rosenthal_potential_change {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (S : ι → Finset E) (i : ι) (T : Finset E) :
    potential G (Function.update S i T) - potential G S =
      cost G (Function.update S i T) i - cost G S i := by sorry

end PriceOfStability.Harmonic

