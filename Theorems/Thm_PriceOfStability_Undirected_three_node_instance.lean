import Definitions.Def_PriceOfStability_Undirected_ThreeNode
open CongestionPoA.AsymSum

namespace PriceOfStability.Undirected

/-- The 3-node example of Sect. 4 (Anshelevich et al., SIAM J. Comput. 38 (2008), p. 1613,
PDF p. 12): for `0 < ε < 1`, "the optimal centralized solution has cost `3 + ε`. However, the
cheapest Nash has cost `4`." That is: some pure Nash equilibrium costs `4` and every one costs at
least `4`; some profile costs `3 + ε` and every profile costs at least `3 + ε`. The ratio
`4/(3 + ε)` tends to `4/3` as `ε → 0`.

**Formalization Note.** The paper leaves the range of `ε` implicit; `0 < ε` is needed for the
`3 + ε` trees not to be equilibria, and `ε < 1` for `3 + ε < 4`. -/
theorem three_node_instance (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (∃ S, IsPureNash (threeNode ε) S ∧ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) S = 4) ∧
    (∀ S, IsPureNash (threeNode ε) S → 4 ≤ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) S) ∧
    (∃ P, IsProfile (threeNode ε) P ∧ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) P = 3 + ε) ∧
    (∀ P, IsProfile (threeNode ε) P → 3 + ε ≤ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) P) := by sorry

end PriceOfStability.Undirected

