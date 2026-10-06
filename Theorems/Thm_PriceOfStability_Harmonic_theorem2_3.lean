import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*, SIAM J.
Comput. 38 (2008), Theorem 2.3, p. 1608 (PDF p. 7): in a fair connection game in which every edge has a
nondecreasing concave cost function `c_e(x)` of its number of users `x`, the price of stability
is at most `H(k)`: some pure Nash equilibrium `S` has `cost(S) ≤ H(k) · cost(P)` for every
strategy vector `P`.

**Formalization Note.** Strategy families are arbitrary (the *Extensions* paragraph, p. 1609);
the graph game is the instance `Σᵢ = {S ⊆ E : S connects Tᵢ}`. `H(k)` is `harmonic` cast to
`ℝ` with `k = Fintype.card ι`. `c_e(0) ≥ 0` (inside `IsConcaveCost`) is implicit in the paper.
The price of stability is stated in existence form, and a profile is assumed to exist. -/
theorem theorem2_3 {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (strategies : ι → Finset (Finset E)) (c : E → ℕ → ℝ) (hc : IsConcaveCost c)
    (hP : ∃ P, IsProfile (fairGame strategies c) P) :
    ∃ S, IsPureNash (fairGame strategies c) S ∧
      ∀ P, IsProfile (fairGame strategies c) P →
        designCost c S ≤ (harmonic (Fintype.card ι) : ℝ) * designCost c P := by sorry

end PriceOfStability.Harmonic

