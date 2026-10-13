import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_Lifts
import Definitions.Def_Disjunctive_HigherDim_BoundRows


namespace Disjunctive.HigherDim

/-- Theorem 7.4 (Balas, *Disjunctive Programming*, Springer 2018, §7.2, p. 93, [99]): for
`K = {x : Ãx ≥ b̃}` the LP relaxation of a mixed 0-1 program with 0-1 index set `N'` (bound rows
`x ≥ 0`, `x_j ≤ 1`, `j ∈ N'`, included in the system, `HasBoundRows`, so that the
Lovász-Schrijver lift multiplies them too), `N(K) ⊆ conv(K ∩ {x_j ∈ {0,1}})` for every `j ∈ N'`.
Corrected: the retired version allowed an arbitrary system `Ax ≥ b` without the bound rows. -/
theorem lovasz_schrijver_one_step_v2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) :
    ∀ j ∈ Nprime, NOp A b Nprime ⊆ convexHull ℝ (Poly A b ∩ ZeroOneSet j) := by sorry

end Disjunctive.HigherDim

