import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*, SIAM J.
Comput. 38 (2008), Theorem 2.1, proof, p. 1607 (PDF p. 6): starting from any strategy vector, a sequence of
improving moves leads to a Nash equilibrium, each move decreasing the potential `Φ` of (2.1); so
from every profile `S₀` there is a pure Nash equilibrium `S` with `Φ(S) ≤ Φ(S₀)`.

**Formalization Note.** Stated for every congestion game. The conclusion is the existence of the
end point of the improving sequence, with its potential bound, which is what the proofs of
Theorems 2.1, 2.3 and 3.1 use. -/
theorem improving_moves_reach_nash {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (S₀ : ι → Finset E) (h₀ : IsProfile G S₀) :
    ∃ S, IsPureNash G S ∧ potential G S ≤ potential G S₀ := by sorry

end PriceOfStability.Harmonic

