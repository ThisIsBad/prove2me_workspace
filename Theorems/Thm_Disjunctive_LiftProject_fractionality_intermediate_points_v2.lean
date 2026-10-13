import Mathlib
import Definitions.Def_Disjunctive_LiftProject_Basic
import Definitions.Def_Disjunctive_LiftProject_BoundRows


namespace Disjunctive.LiftProject

/-- Theorem 6.1 (Balas, *Disjunctive Programming*, Springer 2018, §6.2, p. 81): let
`P = {x : Ãx ≥ b̃}` be the LP relaxation of a mixed 0-1 program with 0-1 index set `N'`, the
bound rows `x ≥ 0` and `x_j ≤ 1` (`j ∈ N'`) being rows of `Ãx ≥ b̃` (`HasBoundRows`), and let
`i₁, i_j ∈ N'`. Put `P₁ := conv(P ∩ {x_{i₁} ∈ {0,1}})` and `P_{1j} := conv(P₁ ∩ {x_{i_j} ∈ {0,1}})`.
If `αx ≥ β` is valid for `P_{1j}` and `x*` is an extreme point of `P₁ ∩ {αx ≥ β}` with
`0 < x*_{i₁} < 1`, then `0 < x*_{i_j} < 1`.
Corrected: the retired version allowed an arbitrary polyhedron `Ãx ≥ b̃` without the 0-1 bounds
and arbitrary coordinates `i₁, i_j`. -/
theorem fractionality_intermediate_points_v2 {n m : ℕ} (Atil : Matrix (Fin m) (Fin n) ℝ)
    (btil : Fin m → ℝ) (Nprime : Finset (Fin n)) (hP : HasBoundRows Atil btil Nprime)
    (i1 ij : Fin n) (hi1 : i1 ∈ Nprime) (hij : ij ∈ Nprime) (α : Fin n → ℝ) (β : ℝ)
    (hValid : ∀ x ∈ SplitConvexify (SplitConvexify (Poly Atil btil) i1) ij, β ≤ dotProduct α x)
    (xstar : Fin n → ℝ)
    (hExt : xstar ∈ Set.extremePoints ℝ
      (SplitConvexify (Poly Atil btil) i1 ∩ {x | β ≤ dotProduct α x}))
    (h1 : 0 < xstar i1 ∧ xstar i1 < 1) :
    0 < xstar ij ∧ xstar ij < 1 := by sorry

end Disjunctive.LiftProject

