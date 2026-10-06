import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_fig11

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*, SIAM J.
Comput. 38 (2008), Sect. 1, p. 1604 (PDF p. 3), Fig. 1.1: with `k ≥ 1` players and `ε > 0`, the instance
of Fig. 1.1 has a unique Nash equilibrium, it costs `H(k) = Σ_{i=1}^k 1/i`, and the profile in
which all players share the common path costs `1 + ε`. Hence the price of stability of this
instance is at least `H(k)/(1 + ε)`, which tends to `H(k)` as `ε → 0` (caption of Fig. 1.1;
"the upper bound of Theorem 2.1 is tight", p. 1608).

**Formalization Note.** The second conjunct is implied by the first together with the
computation of the equilibrium's cost; it is stated separately because it is the claim of the
page. The page's "the optimal solution … for a total cost of 1 + ε" is false for `k = 1`
(the own edge costs `1 < 1 + ε`), so only the existence of a profile of cost `1 + ε` is stated. -/
theorem fig11_unique_nash (k : ℕ) (ε : ℝ) (hk : 1 ≤ k) (hε : 0 < ε) :
    (∃! S, IsPureNash (fig11 k ε) S) ∧
      (∀ S, IsPureNash (fig11 k ε) S →
        designCost (fun e _ => fig11Cost k ε e) S = (harmonic k : ℝ)) ∧
      ∃ P, IsProfile (fig11 k ε) P ∧ designCost (fun e _ => fig11Cost k ε e) P = 1 + ε := by sorry

end PriceOfStability.Harmonic

