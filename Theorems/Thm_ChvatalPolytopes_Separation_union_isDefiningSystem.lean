import Mathlib
import Definitions.Def_ChvatalPolytopes_Shared_StablePolytope

namespace ChvatalPolytopes.Separation

/-- **Theorem 4.1** (Chvátal 1975, p. 141). Let `G₁ = (V₁, E₁)` and `G₂ = (V₂, E₂)` be graphs such
that `G₁ ∩ G₂ = (V₁ ∩ V₂, E₁ ∩ E₂)` is complete. Let (4.1)
`−x_u ≤ 0 (u ∈ V₁)`, `Σ (a_{iu} x_u : u ∈ V₁) ≤ b_i (i ∈ J₁)`
be a defining linear system of `P(G₁)` and (4.2)
`−x_u ≤ 0 (u ∈ V₂)`, `Σ (a_{iu} x_u : u ∈ V₂) ≤ b_i (i ∈ J₂)`
a defining linear system of `P(G₂)`. Then the union of (4.1) and (4.2) is a defining linear
system of `P(G₁ ∪ G₂)`, where `G₁ ∪ G₂ = (V₁ ∪ V₂, E₁ ∪ E₂)`.

Encoding: `G` is the graph `G₁ ∪ G₂` on the vertex type `V = V₁ ∪ V₂` (`hcover`); `G₁` and `G₂`
are the subgraphs of `G` induced on `V₁` and `V₂`. "`G₁ ∩ G₂` is complete" is `hclique`
(`V₁ ∩ V₂` is a clique of `G`), and `G = G₁ ∪ G₂` forces `hsep` (no edge of `G` joins
`V₁ − V₂` to `V₂ − V₁`). Under these hypotheses the induced subgraphs are exactly the paper's
`G₁, G₂`. The rows of (4.1), (4.2) are read on `V` by restricting `x` to `V₁`, `V₂`
(equivalently, coefficients are extended by `0`); the nonnegativity rows of the union are
`−x_u ≤ 0` for all `u ∈ V₁ ∪ V₂ = V`. -/
theorem union_isDefiningSystem {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (V₁ V₂ : Finset V)
    (hcover : V₁ ∪ V₂ = Finset.univ)
    (hclique : G.IsClique ((V₁ ∩ V₂ : Finset V) : Set V))
    (hsep : ∀ u v, u ∈ V₁ → u ∉ V₂ → v ∈ V₂ → v ∉ V₁ → ¬ G.Adj u v)
    {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (a₁ : J₁ → ↥(V₁ : Set V) → ℝ) (b₁ : J₁ → ℝ)
    (a₂ : J₂ → ↥(V₂ : Set V) → ℝ) (b₂ : J₂ → ℝ)
    (h₁ : {x : ↥(V₁ : Set V) → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a₁ i u * x u ≤ b₁ i} =
      Shared.stablePolytope (G.induce (V₁ : Set V)))
    (h₂ : {x : ↥(V₂ : Set V) → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a₂ i u * x u ≤ b₂ i} =
      Shared.stablePolytope (G.induce (V₂ : Set V))) :
    {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ (∀ i, ∑ u : ↥(V₁ : Set V), a₁ i u * x u ≤ b₁ i) ∧
        (∀ i, ∑ u : ↥(V₂ : Set V), a₂ i u * x u ≤ b₂ i)} = Shared.stablePolytope G := by sorry

end ChvatalPolytopes.Separation

