import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_AdjacencyInstance
open scoped NNReal

namespace SingleMachinePrec.VariableCost

open Classical in
/-- Theorem 8.1 (p. 664): approximating the variable cost of `1|prec|∑ w_j C_j` is as hard as
approximating vertex cover. What the proof establishes: let `G` be a graph on `n` vertices,
`r ≥ 1`, `ε > 0`, `k > n² r / ε` with `k ≥ 1`, and `S = adjacencyInstance G k`. If `C` is a
vertex cover of `G^S_P` whose weight is at most `r` times the minimum weight of a vertex cover of
`G^S_P`, then `C_G = {v_i : (v′_i, v″_i) ∈ C}` is a vertex cover of `G` with
`|C_G| ≤ r (τ(G) + n²/k)`, and, if `G` has an edge, `|C_G| ≤ r (1 + n²/k) τ(G) < (r + ε) τ(G)`,
where `τ(G)` is the vertex cover number of `G`. -/
theorem theorem_8_1 {n : ℕ} (G : SimpleGraph (Fin n)) (r ε : ℝ) (k : ℝ≥0)
    (hr : 1 ≤ r) (hε : 0 < ε) (hk1 : 1 ≤ k) (hk : (n : ℝ) ^ 2 * r / ε < (k : ℝ))
    (C : Finset (IncPair (adjacencyInstance G k).P))
    (hC : (vertexCoverGraph (adjacencyInstance G k).P).IsVertexCover (C : Set _))
    (hCr : weight (adjacencyInstance G k) C ≤ r * minCoverWeight (adjacencyInstance G k)) :
    G.IsVertexCover {i | heavy G k i ∈ C} ∧
    ((Finset.univ.filter (fun i => heavy G k i ∈ C)).card : ℝ) ≤
      r * ((G.vertexCoverNum.toNat : ℝ) + (n : ℝ) ^ 2 / (k : ℝ)) ∧
    (G.edgeSet.Nonempty →
      ((Finset.univ.filter (fun i => heavy G k i ∈ C)).card : ℝ) ≤
          r * (1 + (n : ℝ) ^ 2 / (k : ℝ)) * (G.vertexCoverNum.toNat : ℝ) ∧
        r * (1 + (n : ℝ) ^ 2 / (k : ℝ)) * (G.vertexCoverNum.toNat : ℝ) <
          (r + ε) * (G.vertexCoverNum.toNat : ℝ)) := by sorry

end SingleMachinePrec.VariableCost

