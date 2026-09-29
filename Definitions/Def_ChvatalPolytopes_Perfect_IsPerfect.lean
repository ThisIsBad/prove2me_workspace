import Mathlib
import Definitions.Def_ChvatalPolytopes_Perfect_StablePolytope

namespace ChvatalPolytopes.Perfect

/-- `m` is the maximum of `{cx : x ∈ S(G)}`: some stable-set incidence vector `x` has
`Σ_u c_u x_u = m`, and every one has `Σ_u c_u x_u ≤ m`. -/
def IsStableMax {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : V → ℝ)
    (m : ℝ) : Prop :=
  (∃ x ∈ stableVectors G, ∑ u, c u * x u = m) ∧ ∀ x ∈ stableVectors G, ∑ u, c u * x u ≤ m

/-- **Perfect** (or α-perfect) graph (Chvátal 1975, p. 140): for every zero–one valued vector
`c = (c_u : u ∈ V)`, the maximum of `{cx : x ∈ S(G)}` is equal to the minimum of
`{Σ (λ_W : W ∈ C(G)) : λ_W ∈ {0, 1} and, for each u ∈ V, Σ (λ_W : u ∈ W ∈ C(G)) ≥ c_u}`.

Here "max = min" is spelled out: there is a value `m` which is the maximum over `S(G)`, which is
attained by some zero–one `λ` covering `c`, and which is at most the objective of every such
`λ`. The weights `λ : Finset V → ℝ` are only read on `C(G) = maximalCliques G`. -/
def IsPerfect {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ c : V → ℝ, (∀ u, c u = 0 ∨ c u = 1) →
    ∃ m : ℝ, IsStableMax G c m ∧
      (∃ lam : Finset V → ℝ, (∀ W ∈ maximalCliques G, lam W = 0 ∨ lam W = 1) ∧
        (∀ u, c u ≤ ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W) ∧
        ∑ W ∈ maximalCliques G, lam W = m) ∧
      (∀ lam : Finset V → ℝ, (∀ W ∈ maximalCliques G, lam W = 0 ∨ lam W = 1) →
        (∀ u, c u ≤ ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W) →
        m ≤ ∑ W ∈ maximalCliques G, lam W)

end ChvatalPolytopes.Perfect
