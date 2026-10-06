import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*, SIAM J.
Comput. 38 (2008), Theorem 2.3, proof, p. 1608 (PDF p. 7): for nondecreasing concave edge costs,
`cost(S) ≤ Φ(S) ≤ H(k) · cost(S)` for all strategies `S`, where `Φ` is the potential (2.1)
of the fair game, `cost(S)` the cost of the designed network and `H(k) = 1 + 1/2 + … + 1/k` with
`k` the number of players.

**Formalization Note.** `H(k)` is Mathlib's `harmonic` (`ℚ`-valued) cast to `ℝ`, with
`k = Fintype.card ι`. The hypothesis `c_e(0) ≥ 0` in `IsConcaveCost` is implicit in the
paper (see that definition). Stated for every strategy vector `S`. -/
theorem cost_le_potential_le_harmonic {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (strategies : ι → Finset (Finset E)) (c : E → ℕ → ℝ)
    (hc : IsConcaveCost c) (S : ι → Finset E) :
    designCost c S ≤ potential (fairGame strategies c) S ∧
      potential (fairGame strategies c) S ≤ (harmonic (Fintype.card ι) : ℝ) * designCost c S := by sorry

end PriceOfStability.Harmonic

