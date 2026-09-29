import Mathlib
import Definitions.Def_ChvatalPolytopes_Shared_StablePolytope
import Definitions.Def_ChvatalPolytopes_Substitution_substitute

namespace ChvatalPolytopes.Substitution

/-- **Theorem 5.1** (Chvátal 1975, p. 145). Let `G₁ = (V₁, E₁)` and `G₂ = (V₂, E₂)` be graphs with
`V₁ ∩ V₂ = ∅`. For `k ∈ {1, 2}`, let
`−x_u ≤ 0 (u ∈ V_k)`, `Σ (a_{iu} x_u : u ∈ V_k) ≤ b_i (i ∈ J_k)`
be a defining linear system of `P(G_k)`. Let `v` be a vertex of `G₁` and let `G` be the graph
obtained from `G₁` by substituting `G₂` for `v`. For each `i ∈ J₁`, set
`a⁺_{iv} = max {a_{iv}, 0}`. Then
`−x_u ≤ 0 (u ∈ V₂ ∪ (V₁ − {v}))`,
`a⁺_{iv} Σ (a_{ju} x_u : u ∈ V₂) + b_j Σ (a_{iu} x_u : u ∈ V₁ − {v}) ≤ b_i b_j
(i ∈ J₁, j ∈ J₂)` (5.1)
is a defining linear system of `P(G)`, i.e. its solution set equals `P(G) = conv S(G)`.

Conventions: vertices of `G` are `{u : V₁ // u ≠ v} ⊕ V₂` (`inl` = `V₁ − {v}`, `inr` = `V₂`), so
`V₁ ∩ V₂ = ∅` is built in; `J₁`, `J₂` are finite index types, coefficients real; "defining linear
system of `P(G_k)`" is the set equality `h₁`/`h₂`.

**Implicit hypothesis made explicit:** `[Nonempty V₂]`. The paper's graphs have nonempty vertex
sets (Harary), and its proof picks "an arbitrary vertex `w` of `G₂`" (p. 148). With `V₂ = ∅` the
statement is false (take `J₂ = ∅` and `V₁ ≠ {v}`: then (5.1) is only `x ≥ 0`). -/
theorem substitution_defining_system {V₁ V₂ : Type*} [Fintype V₁] [DecidableEq V₁]
    [Fintype V₂] [DecidableEq V₂] [Nonempty V₂] (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (a₁ : J₁ → V₁ → ℝ) (b₁ : J₁ → ℝ) (a₂ : J₂ → V₂ → ℝ) (b₂ : J₂ → ℝ)
    (h₁ : {x : V₁ → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a₁ i u * x u ≤ b₁ i} = Shared.stablePolytope G₁)
    (h₂ : {x : V₂ → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ j, ∑ u, a₂ j u * x u ≤ b₂ j} = Shared.stablePolytope G₂)
    (v : V₁) :
    {x : {u : V₁ // u ≠ v} ⊕ V₂ → ℝ |
        (∀ u, 0 ≤ x u) ∧
        ∀ i j, max (a₁ i v) 0 * ∑ u : V₂, a₂ j u * x (.inr u)
          + b₂ j * ∑ w : {u : V₁ // u ≠ v}, a₁ i w * x (.inl w) ≤ b₁ i * b₂ j} =
      Shared.stablePolytope (substitute G₁ v G₂) := by sorry

end ChvatalPolytopes.Substitution

