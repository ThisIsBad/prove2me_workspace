import Mathlib
import Definitions.Def_Disjunctive_LiftProject_Basic

namespace Disjunctive.LiftProject

/-- Theorem 6.1 (Balas §6.2, p. 81, [32]): if `αx ≥ β` is valid for `P_{1j}` and `x*` is an
extreme point of `P_1 ∩ {αx ≥ β}` with `0 < x*_1 < 1`, then `0 < x*_j < 1` too. -/
theorem fractionality_intermediate_points {n m : ℕ} (Atil : Matrix (Fin m) (Fin n) ℝ)
    (btil : Fin m → ℝ) (i1 ij : Fin n) (α : Fin n → ℝ) (β : ℝ)
    (hValid : ∀ x ∈ SplitConvexify (SplitConvexify (Poly Atil btil) i1) ij, β ≤ dotProduct α x)
    (xstar : Fin n → ℝ)
    (hExt : xstar ∈ Set.extremePoints ℝ
      (SplitConvexify (Poly Atil btil) i1 ∩ {x | β ≤ dotProduct α x}))
    (h1 : 0 < xstar i1 ∧ xstar i1 < 1) :
    0 < xstar ij ∧ xstar ij < 1 := by sorry

end Disjunctive.LiftProject

