import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_AdjacencyInstance
open scoped NNReal

namespace SingleMachinePrec.VariableCost

open Classical in
/-- §8, p. 664 (proof of Theorem 8.1). For the instance `S = adjacencyInstance G k` with
`k ≥ 1`: every node `(v′_i, v″_i)` of `G^S_P` has weight `1`; every other node has weight at
most `1/k`; and the total weight of the other ("light") nodes is at most `n²/k`. -/
theorem light_vertices_weight {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0) (hk : 1 ≤ k) :
    (∀ i : Fin n, vertexWeight (adjacencyInstance G k) (heavy G k i) = 1) ∧
    (∀ u : IncPair (adjacencyInstance G k).P, (∀ i : Fin n, u ≠ heavy G k i) →
      vertexWeight (adjacencyInstance G k) u ≤ 1 / (k : ℝ)) ∧
    weight (adjacencyInstance G k)
        (Finset.univ.filter (fun u => ∀ i : Fin n, u ≠ heavy G k i)) ≤
      (n : ℝ) ^ 2 / (k : ℝ) := by sorry

end SingleMachinePrec.VariableCost

