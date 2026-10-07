import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network
import Definitions.Def_FordFulkerson58_ArcChain_LP
import Definitions.Def_FordFulkerson58_ArcChain_Labeling

namespace FordFulkerson58.ArcChain

/-- §3, pp. 1779–1780, the shortest-chain pricing test. Let `β` be a feasible basis of the arc-chain
program (2)–(3) with basic solution `z` and simplex multipliers `α` (4), all `α_r ≥ 0`, and use the
`α_r` as arc lengths. Then
(a) for every commodity, the labeling process from the commodity's sources terminates;
(b) if for every commodity the final labels at all its sinks are at least `1`, the basis is optimal;
(c) if for some commodity the final label of a sink `t` is below `1`, there is a chain from the
commodity's sources to `t` of length equal to that label, whose column is not basic and has positive
reduced cost `1 − ∑_r α_r a_rs`, so it may be introduced into the basis. -/
theorem shortest_chain_pricing_test {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] (N : Network V E ι)
    (β : E → Col N ⊕ E) (hβ : IsUnit (basisMatrix N β).det)
    (z : Col N ⊕ E → ℝ) (hz : IsBasicFeasibleSolution N β z)
    (α : E → ℝ) (h4 : IsSimplexMultiplier N β α)
    (hα : ∀ r, 0 ≤ α r) :
    (∀ k : ι, ¬ ∃ f : ℕ → V → WithTop ℝ,
        f 0 = initLabel (N.src k) ∧ ∀ i, RelaxStep N α (f i) (f (i + 1))) ∧
    (∀ lab : ι → V → WithTop ℝ,
        (∀ k, Relation.ReflTransGen (RelaxStep N α) (initLabel (N.src k)) (lab k) ∧
          IsTerminal N α (lab k)) →
        (∀ k, ∀ t ∈ N.snk k, (1 : WithTop ℝ) ≤ lab k t) →
        ∀ (x : Col N → ℝ) (y : E → ℝ), Feasible N x y → ∑ s, x s ≤ ∑ s, z (Sum.inl s)) ∧
    (∀ (k : ι) (lab : V → WithTop ℝ),
        Relation.ReflTransGen (RelaxStep N α) (initLabel (N.src k)) lab → IsTerminal N α lab →
        ∀ t ∈ N.snk k, lab t < 1 →
        ∃ (C : Finset E) (h : IsCommodityChain N k C), IsChainFrom N (N.src k) t C ∧
          ((chainLength α C : ℝ) : WithTop ℝ) = lab t ∧
          0 < reducedCost N α (Sum.inl ⟨(k, C), h⟩) ∧
          (Sum.inl ⟨(k, C), h⟩ : Col N ⊕ E) ∉ Set.range β) := by sorry

end FordFulkerson58.ArcChain

