import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_AdjacencyInstance
open scoped NNReal

namespace SingleMachinePrec.VariableCost

/-- §8, p. 664 (proof of Theorem 8.1). For the instance `S = adjacencyInstance G k`:
(1) two nodes `(v′_i, v″_i)` and `(v′_j, v″_j)` are adjacent in `G^S_P` if and only if
`{v_i, v_j} ∈ E`; (2) if `k > 1`, the subgraph of `G^S_P` induced by the nodes of weight `1`
is isomorphic to `G`, by an isomorphism sending `(v′_i, v″_i)` to `v_i`. -/
theorem heavy_subgraph_iso {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0) :
    (∀ i j : Fin n,
      (vertexCoverGraph (adjacencyInstance G k).P).Adj (heavy G k i) (heavy G k j) ↔
        G.Adj i j) ∧
    (1 < k →
      ∃ f : (vertexCoverGraph (adjacencyInstance G k).P).induce
          {u | vertexWeight (adjacencyInstance G k) u = 1} ≃g G,
        ∀ (i : Fin n) (h : heavy G k i ∈ {u | vertexWeight (adjacencyInstance G k) u = 1}),
          f ⟨heavy G k i, h⟩ = i) := by sorry

end SingleMachinePrec.VariableCost

