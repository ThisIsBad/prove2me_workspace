import Mathlib
import Definitions.Def_ChvatalPolytopes_Shared_StablePolytope
import Definitions.Def_ChvatalPolytopes_Substitution_substitute

namespace ChvatalPolytopes.Substitution

/-- **Validity of (5.1)** (Chvátal 1975, §5, p. 145, proof of Theorem 5.1: "each `x ∈ S(G)` is a
solution of (5.1)").

Hypotheses of Theorem 5.1: for `k ∈ {1, 2}` the system `−x_u ≤ 0 (u ∈ V_k)`,
`Σ (a_{iu} x_u : u ∈ V_k) ≤ b_i (i ∈ J_k)` is a defining linear system of `P(G_k)`; `v` is a
vertex of `G₁`, `G` is obtained from `G₁` by substituting `G₂` for `v`, and
`a⁺_{iv} = max {a_{iv}, 0}`. Conclusion: every `x ∈ S(G)` satisfies
`x_u ≥ 0 (u ∈ V₂ ∪ (V₁ − {v}))` and, for all `i ∈ J₁`, `j ∈ J₂`,
`a⁺_{iv} Σ (a_{ju} x_u : u ∈ V₂) + b_j Σ (a_{iu} x_u : u ∈ V₁ − {v}) ≤ b_i b_j`.

Vertices of `G` are `{u : V₁ // u ≠ v} ⊕ V₂` (`inl` = `V₁ − {v}`, `inr` = `V₂`). The hypothesis
`V₂ ≠ ∅` of the goal theorem is not needed for this half and is not assumed. -/
theorem substitution_system_valid {V₁ V₂ : Type*} [Fintype V₁] [DecidableEq V₁]
    [Fintype V₂] [DecidableEq V₂] (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (a₁ : J₁ → V₁ → ℝ) (b₁ : J₁ → ℝ) (a₂ : J₂ → V₂ → ℝ) (b₂ : J₂ → ℝ)
    (h₁ : {x : V₁ → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a₁ i u * x u ≤ b₁ i} = Shared.stablePolytope G₁)
    (h₂ : {x : V₂ → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ j, ∑ u, a₂ j u * x u ≤ b₂ j} = Shared.stablePolytope G₂)
    (v : V₁) :
    ∀ x ∈ Shared.stableVectors (substitute G₁ v G₂),
      (∀ u, 0 ≤ x u) ∧
      ∀ i j, max (a₁ i v) 0 * ∑ u : V₂, a₂ j u * x (.inr u)
          + b₂ j * ∑ w : {u : V₁ // u ≠ v}, a₁ i w * x (.inl w) ≤ b₁ i * b₂ j := by sorry

end ChvatalPolytopes.Substitution
