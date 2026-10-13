import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_BoundRows


namespace Disjunctive.HigherDim

/-- Corollary 7.3 (Balas, *Disjunctive Programming*, Springer 2018, §7.1, p. 93): for
`K = {x : Ãx ≥ b̃}` the LP relaxation of a mixed 0-1 program with 0-1 index set `N'` (bound rows
`x ≥ 0`, `x_j ≤ 1`, `j ∈ N'`, included in the system, `HasBoundRows`), iterating the
one-variable convexification over all of `N'` (in any duplicate-free order) gives
`P_{1,…,p}(K) = conv(K₀)`.
Corrected: the retired version allowed an arbitrary polyhedron `Ax ≥ b` without the bounds. -/
theorem full_split_convexification_v2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) (l : List (Fin n)) (hnd : l.Nodup)
    (heq : l.toFinset = Nprime) :
    IteratedSplit (Poly A b) l = convexHull ℝ (K0Set A b Nprime) := by sorry

end Disjunctive.HigherDim

