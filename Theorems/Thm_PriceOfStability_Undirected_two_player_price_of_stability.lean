import Definitions.Def_PriceOfStability_Undirected_ThreeNode
open CongestionPoA.AsymSum

namespace PriceOfStability.Undirected

/-- Claim 4.1 and its tightness example (Anshelevich et al., SIAM J. Comput. 38 (2008), Sect. 4,
p. 1613, PDF p. 12): "The price of stability is at most 4/3 in a fair connection game with two
players in an undirected graph, each having two terminals with one terminal in common", and the
3-node example shows the bound is tight.

1. For every finite undirected graph with nonnegative edge costs, common terminal `s` and personal
   terminals `t₁, t₂` that admits a profile, some pure Nash equilibrium `S` satisfies
   `cost(S) ≤ (4/3)·cost(P)` for every profile `P`.
2. For `0 < ε < 1`, in the 3-node example the cheapest Nash equilibrium costs `4` and the optimum
   costs `3 + ε`.

**Formalization Note.** "Price of stability ≤ 4/3" is stated in existence form (no division by the
optimum). `cost(S)` is the total cost of the edges used by at least one player. Players `0`, `1` are
the paper's 1, 2; strategies are arbitrary connecting edge sets of `G`. -/
theorem two_player_price_of_stability :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : Sym2 V → ℝ) (s : V)
        (t : Fin 2 → V), (∀ e, 0 ≤ c e) →
        (∃ P, IsProfile (twoPlayerGame G c s t) P) →
        ∃ S, IsPureNash (twoPlayerGame G c s t) S ∧
          ∀ P, IsProfile (twoPlayerGame G c s t) P →
            PriceOfStability.Harmonic.designCost (fun e _ => c e) S ≤ 4 / 3 * PriceOfStability.Harmonic.designCost (fun e _ => c e) P) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 →
      (∃ S, IsPureNash (threeNode ε) S ∧ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) S = 4) ∧
      (∀ S, IsPureNash (threeNode ε) S → 4 ≤ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) S) ∧
      (∃ P, IsProfile (threeNode ε) P ∧ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) P = 3 + ε) ∧
      (∀ P, IsProfile (threeNode ε) P → 3 + ε ≤ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) P)) := by sorry

end PriceOfStability.Undirected

