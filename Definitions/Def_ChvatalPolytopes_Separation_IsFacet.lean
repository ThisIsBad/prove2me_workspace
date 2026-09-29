import Mathlib

namespace ChvatalPolytopes.Separation

/-- **Facet** (Chvátal 1975, p. 138). A finite linear system
`Σ (A_{ju} x_u : u ∈ V) ≤ B_j (j ∈ J)` is a *defining linear system* of `P ⊆ ℝ^V` when its set
of solutions is exactly `P`. The inequality `Σ (a_u x_u : u ∈ V) ≤ b` is a *facet* of `P` if and
only if every defining linear system of `P` includes, for some positive `t`, the inequality
`Σ (t a_u x_u : u ∈ V) ≤ t b`.

Defining systems are indexed by an arbitrary finite index type `J`, with real coefficients and
no separate nonnegativity rows (a nonnegativity inequality, if present, is one of the rows). -/
def IsFacet {V : Type*} [Fintype V] (P : Set (V → ℝ)) (a : V → ℝ) (b : ℝ) : Prop :=
  ∀ (J : Type) [Fintype J] (A : J → V → ℝ) (B : J → ℝ),
    {x : V → ℝ | ∀ j, ∑ u, A j u * x u ≤ B j} = P →
      ∃ j : J, ∃ t : ℝ, 0 < t ∧ (∀ u, A j u = t * a u) ∧ B j = t * b

end ChvatalPolytopes.Separation
