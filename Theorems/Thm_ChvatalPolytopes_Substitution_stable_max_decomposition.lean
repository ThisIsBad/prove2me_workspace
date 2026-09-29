import Mathlib
import Definitions.Def_ChvatalPolytopes_Shared_StablePolytope
import Definitions.Def_ChvatalPolytopes_Substitution_substitute

namespace ChvatalPolytopes.Substitution

/-- **Decomposition of the optimum** (Chvátal 1975, §5, pp. 145–146, proof of Theorem 5.1).
Let `G` be obtained from `G₁` by substituting `G₂` for the vertex `v` of `G₁`, and set
`W = V₁ − {v}`. Let `c = (c_u : u ∈ V₂ ∪ W)` be an integer-valued vector, `d_u = max {c_u, 0}`,
`m = max {cx : x ∈ S(G)}`, and
* `m₀ = max {Σ (d_u x_u : u ∈ W) : (x_u : u ∈ V₁) ∈ S(G₁), x_v = 0}`,
* `m₁ = max {Σ (d_u x_u : u ∈ W) : (x_u : u ∈ V₁) ∈ S(G₁), x_v = 1}`,
* `m₂ = max {Σ (d_u x_u : u ∈ V₂) : (x_u : u ∈ V₂) ∈ S(G₂)}`.
Then `m = max {Σ (d_u x_u : u ∈ V₂ ∪ W) : x ∈ S(G)}` and `m = max {m₀, m₁ + m₂}`.

Vertices of `G` are `{u : V₁ // u ≠ v} ⊕ V₂` (`inl` = `W`, `inr` = `V₂`). Each maximum is written
as `sSup` of the (finite) image set; every one of these sets is finite and nonempty (`S(G)`,
`S(G₂)` and `{x ∈ S(G₁) : x_v = 0}` contain the zero vector, `{x ∈ S(G₁) : x_v = 1}` contains the
incidence vector of `{v}`), so each `sSup` is an attained maximum. -/
theorem stable_max_decomposition {V₁ V₂ : Type*} [Fintype V₁] [DecidableEq V₁]
    [Fintype V₂] [DecidableEq V₂] (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) (v : V₁)
    (c : {u : V₁ // u ≠ v} ⊕ V₂ → ℤ) :
    let d : {u : V₁ // u ≠ v} ⊕ V₂ → ℤ := fun u => max (c u) 0
    let m : ℝ := sSup ((fun x => ∑ u, (c u : ℝ) * x u) '' Shared.stableVectors (substitute G₁ v G₂))
    let m₀ : ℝ := sSup ((fun x : V₁ → ℝ => ∑ w : {u : V₁ // u ≠ v}, (d (.inl w) : ℝ) * x w) ''
      {x | x ∈ Shared.stableVectors G₁ ∧ x v = 0})
    let m₁ : ℝ := sSup ((fun x : V₁ → ℝ => ∑ w : {u : V₁ // u ≠ v}, (d (.inl w) : ℝ) * x w) ''
      {x | x ∈ Shared.stableVectors G₁ ∧ x v = 1})
    let m₂ : ℝ := sSup ((fun x : V₂ → ℝ => ∑ u, (d (.inr u) : ℝ) * x u) '' Shared.stableVectors G₂)
    m = sSup ((fun x => ∑ u, (d u : ℝ) * x u) '' Shared.stableVectors (substitute G₁ v G₂)) ∧
      m = max m₀ (m₁ + m₂) := by sorry

end ChvatalPolytopes.Substitution

