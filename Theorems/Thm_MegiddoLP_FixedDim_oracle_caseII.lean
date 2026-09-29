import Mathlib
import Definitions.Def_Polyhedron
import Definitions.Def_MegiddoLP_FixedDim_Infeasibility

/-!
Megiddo, J. ACM 31 (1984), §4 p. 125, Case II of the oracle. The paper's `x_d` is the last
coordinate `Fin.last d` of `Fin (d + 1)`; the tested hyperplane is `{x_d = 0}`. Systems (1)
and (2) of the page are `∃ y, y_d = 1 ∧ Aᵢ ⬝ᵥ y ≥ 0 (i ∈ I')` and
`∃ z, z_d = -1 ∧ Aᵢ ⬝ᵥ z ≥ 0 (i ∈ I')`. The side is stated in the corrected direction:
(1) feasible puts every point of smaller infeasibility in `{x_d > 0}`.
-/

open Matrix LinearOptimization

namespace MegiddoLP.FixedDim

/-- **Oracle, Case II.** Let the system `Ax ≥ b` (at least one row) have no solution on
`{x_d = 0}`, let `x'` with `x'_d = 0` minimize `f = infeas A b` on `{x_d = 0}`, and let
`I' = {i | f(x') = bᵢ - Aᵢ ⬝ᵥ x'}`. Then
1. if (1) is feasible, every `w` with `f(w) < f(x')` has `w_d > 0`;
2. if (2) is feasible, every `w` with `f(w) < f(x')` has `w_d < 0`;
3. if (1) and (2) are both feasible or both infeasible, `x'` minimizes `f` on all of `ℝ^d`
   and `Ax ≥ b` is infeasible. -/
theorem oracle_caseII {n d : ℕ} (A : Matrix (Fin (n + 1)) (Fin (d + 1)) ℝ)
    (b : Fin (n + 1) → ℝ) (x' : Fin (d + 1) → ℝ)
    (hinf : polyhedron A b ∩ {x | x (Fin.last d) = 0} = ∅)
    (hx' : x' (Fin.last d) = 0)
    (hmin : ∀ w : Fin (d + 1) → ℝ, w (Fin.last d) = 0 → infeas A b x' ≤ infeas A b w) :
    ((∃ y : Fin (d + 1) → ℝ, y (Fin.last d) = 1 ∧
        ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ y) →
      ∀ w, infeas A b w < infeas A b x' → 0 < w (Fin.last d)) ∧
    ((∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
        ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ z) →
      ∀ w, infeas A b w < infeas A b x' → w (Fin.last d) < 0) ∧
    (((∃ y : Fin (d + 1) → ℝ, y (Fin.last d) = 1 ∧
        ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ y) ↔
      (∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
        ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ z)) →
      (∀ w, infeas A b x' ≤ infeas A b w) ∧ polyhedron A b = ∅) := by sorry

end MegiddoLP.FixedDim
