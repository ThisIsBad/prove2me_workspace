import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice

namespace KannanLattice.Core

/-- Proposition 4.2 of Kannan (1987), p. 23: for a lattice `L(b)` in `ℝᵏ` and any `b₀ ∈ ℝᵏ` with
orthogonal projection `b̄₀` onto `span_ℝ(b)`, some lattice point `v` satisfies
`|v − b̄₀| ≤ ½ (Σ_j b_j(j)²)^{1/2}`, and hence `|b̄₀ − v| ≤ (√m/2) b_i(i)` for every `i` at which
`b_i(i)` is maximal. (The paper's second sentence has `b₀` for `b̄₀`; corrected here.) -/
theorem exists_lattice_point_near_projection (m k : ℕ)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b)
    (b₀ : EuclideanSpace ℝ (Fin k)) :
    ∃ v ∈ lattice b,
      ‖v - (Submodule.span ℝ (Set.range b)).starProjection b₀‖ ≤
          (1 / 2 : ℝ) * Real.sqrt (∑ j, gsLen b j ^ 2) ∧
      ∀ i : Fin m, (∀ j : Fin m, gsLen b j ≤ gsLen b i) →
        ‖(Submodule.span ℝ (Set.range b)).starProjection b₀ - v‖ ≤
          Real.sqrt m / 2 * gsLen b i := by sorry

end KannanLattice.Core

