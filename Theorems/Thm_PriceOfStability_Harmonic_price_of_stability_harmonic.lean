import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_fig11

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*, SIAM J.
Comput. 38 (2008), Theorem 2.1, p. 1607 (PDF p. 6), with its tightness ("Recall from the example in
Figure 1.1 that the upper bound of Theorem 2.1 is tight", p. 1608 (PDF p. 7); Fig. 1.1, p. 1604
(PDF p. 3)).

1. The price of stability of the fair connection game is at most `H(k)`: for every game with
   nonnegative constant edge costs `c_e` in which a profile exists, some pure Nash equilibrium
   `S` has `cost(S) ≤ H(k) · cost(P)` for every profile `P`, `k` the number of players.
2. Tightness: for every `k ≥ 1` and `ε > 0` the instance of Fig. 1.1 has a Nash equilibrium,
   every Nash equilibrium costs `H(k)`, and some profile costs `1 + ε`.

**Formalization Note.** Strategy families are arbitrary families of edge sets (*Extensions*,
p. 1609); the directed-graph game is the instance `Σᵢ = {S ⊆ E : S connects Tᵢ}`. Player and
edge types are quantified in `Type`. `H(k)` is Mathlib's `harmonic` cast to `ℝ`,
`k = Fintype.card ι`. The price of stability is in existence form (never "every equilibrium":
the price of anarchy is `k`), without dividing by the optimum. -/
theorem price_of_stability_harmonic :
    (∀ {ι E : Type} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
      (strategies : ι → Finset (Finset E)) (c : E → ℝ), (∀ e, 0 ≤ c e) →
      (∃ P, IsProfile (fairGame strategies (fun e _ => c e)) P) →
      ∃ S, IsPureNash (fairGame strategies (fun e _ => c e)) S ∧
        ∀ P, IsProfile (fairGame strategies (fun e _ => c e)) P →
          designCost (fun e _ => c e) S ≤
            (harmonic (Fintype.card ι) : ℝ) * designCost (fun e _ => c e) P) ∧
    (∀ (k : ℕ) (ε : ℝ), 1 ≤ k → 0 < ε →
      (∃ S, IsPureNash (fig11 k ε) S) ∧
      (∀ S, IsPureNash (fig11 k ε) S →
        designCost (fun e _ => fig11Cost k ε e) S = (harmonic k : ℝ)) ∧
      ∃ P, IsProfile (fig11 k ε) P ∧ designCost (fun e _ => fig11Cost k ε e) P = 1 + ε) := by sorry

end PriceOfStability.Harmonic

