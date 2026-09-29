import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_KannanLattice_Core_IsReduced

namespace KannanLattice.Core

/-- Proposition 4.3 of Kannan (1987), pp. 23–24, with the proof's explicit candidate set `T` and
`m ≥ 2`. Let `b` be a reduced basis (Definition 2.6) of a lattice in `ℝᵏ`, `b₀ ∈ ℝᵏ`, `b̄₀` its
projection onto `span_ℝ(b)`, and `i` an index with `b_i(i) = max_j b_j(j)`. Let `T` be the set of
integer tails `μ = (μ_j)_{j ≥ i}` with `|P_i(Σ_{j ≥ i} μ_j b_j − b̄₀)| ≤ (√m/2) b_i(i)`, where `P_i`
projects orthogonally to `span(b_j : j < i)`. Then `T` is finite with at most `m^{m−i}` elements
(0-based `i`; the paper's `n^{n−i+1}`), and the tail of the coefficient vector of every closest
lattice point to `b₀` lies in `T`. -/
theorem closest_point_tail_mem_candidates (m k : ℕ) (hm : 2 ≤ m)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b) (hred : IsReduced b)
    (b₀ : EuclideanSpace ℝ (Fin k)) (i : Fin m) (hi : ∀ j : Fin m, gsLen b j ≤ gsLen b i) :
    let T : Set ({j : Fin m // i ≤ j} → ℤ) :=
      {μ | ‖projOrth b i ((∑ j : {j : Fin m // i ≤ j}, (μ j : ℝ) • b j) -
              (Submodule.span ℝ (Set.range b)).starProjection b₀)‖ ≤
            Real.sqrt m / 2 * gsLen b i}
    T.Finite ∧ T.ncard ≤ m ^ (m - (i : ℕ)) ∧
      ∀ lam : Fin m → ℤ,
        (∀ w ∈ lattice b, ‖(∑ j, (lam j : ℝ) • b j) - b₀‖ ≤ ‖w - b₀‖) →
          (fun j : {j : Fin m // i ≤ j} => lam j) ∈ T := by sorry

end KannanLattice.Core

