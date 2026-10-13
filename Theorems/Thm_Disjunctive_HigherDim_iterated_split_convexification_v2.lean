import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_BoundRows


namespace Disjunctive.HigherDim

/-- Theorem 7.2 (Balas, *Disjunctive Programming*, Springer 2018, §7.1, p. 93): for
`K = {x : Ãx ≥ b̃}` the LP relaxation of a mixed 0-1 program with 0-1 index set `N'` (bound rows
`x ≥ 0`, `x_j ≤ 1`, `j ∈ N'`, included in the system, `HasBoundRows`), applying the
one-variable convexification `P_j` successively along a duplicate-free sequence `i₁,…,i_t` of
0-1 indices gives `P_{i₁,…,i_t}(K) = conv(K ∩ {x : x_j ∈ {0,1}, j = i₁,…,i_t})`.
Corrected: the retired version allowed an arbitrary polyhedron `Ax ≥ b` (no bounds) and arbitrary
coordinates; the book's sequence consists of 0-1 variables of the mixed 0-1 program. -/
theorem iterated_split_convexification_v2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime)
    (l : List (Fin n)) (hnd : l.Nodup) (hl : ∀ j ∈ l, j ∈ Nprime) :
    IteratedSplit (Poly A b) l = convexHull ℝ (Poly A b ∩ ⋂ j ∈ l.toFinset, ZeroOneSet j) := by
  sorry

end Disjunctive.HigherDim

