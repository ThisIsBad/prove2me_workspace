import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_BoundRows


namespace Disjunctive.HigherDim

/-- Theorem 7.1 (Balas, *Disjunctive Programming*, Springer 2018, §7.1, p. 92): for
`K = {x : Ãx ≥ b̃}` the LP relaxation of a mixed 0-1 program with 0-1 index set `N'` (the bound
rows `x ≥ 0` and `x_j ≤ 1`, `j ∈ N'`, are rows of the system, `HasBoundRows`) and `j ∈ N'`, the
projection `P_j(K)` of the nonlinear 3-step construction (multiply `Ãx ≥ b̃` by `1 - x_j` and
`x_j`, linearize, project) equals `conv(K ∩ {x_j ∈ {0,1}})`.
Corrected: the retired version allowed an arbitrary system `Ax ≥ b`, without the bound rows the
book folds into `Ãx ≥ b̃`, and an arbitrary coordinate `j`. -/
theorem lift_and_project_one_var_v2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) (j : Fin n) (hj : j ∈ Nprime) :
    Pj A b j = convexHull ℝ (Poly A b ∩ ZeroOneSet j) := by sorry

end Disjunctive.HigherDim

