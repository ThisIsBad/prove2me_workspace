import Mathlib
import Definitions.Def_Polyhedron

/-!
Megiddo, J. ACM 31 (1984), §4 p. 124, Case I of the oracle. The paper's `x_d` is the last
coordinate `Fin.last d` of `Fin (d + 1)`; the tested hyperplane is `{x_d = 0}`. The auxiliary
objective is `c ⬝ᵥ z` with `z_d = ±1`, i.e. the page's `Σ_{j<d} c_j z_j` corrected by the term
`± c_d`.
-/

open Matrix LinearOptimization

namespace MegiddoLP.FixedDim

/-- **Oracle, Case I.** Let `x*` be optimal for `minimize cᵀx` over the feasible points of
`Ax ≥ b` lying on `{x_d = 0}`, and let `I = {i | Aᵢ ⬝ᵥ x* = bᵢ}`. Then
1. some feasible `y` with `y_d > 0` has `cᵀy < cᵀx*` iff some `z` with `z_d = 1`,
   `Aᵢ ⬝ᵥ z ≥ 0` for `i ∈ I` has `cᵀz < 0`;
2. the same with `y_d < 0` and `z_d = -1`;
3. the two auxiliary systems of 1 and 2 do not both have a solution of negative value;
4. if neither does, `x*` is optimal for the original program. -/
theorem oracle_caseI {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℝ) (b : Fin n → ℝ)
    (c xs : Fin (d + 1) → ℝ)
    (hxs : IsLpOptimal c (polyhedron A b ∩ {x | x (Fin.last d) = 0}) xs) :
    ((∃ y ∈ polyhedron A b, 0 < y (Fin.last d) ∧ c ⬝ᵥ y < c ⬝ᵥ xs) ↔
      ∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = 1 ∧
        (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0) ∧
    ((∃ y ∈ polyhedron A b, y (Fin.last d) < 0 ∧ c ⬝ᵥ y < c ⬝ᵥ xs) ↔
      ∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
        (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0) ∧
    ¬ ((∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = 1 ∧
          (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0) ∧
       (∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
          (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0)) ∧
    ((¬ ∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = 1 ∧
          (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0) →
     (¬ ∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
          (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0) →
     IsLpOptimal c (polyhedron A b) xs) := by sorry

end MegiddoLP.FixedDim
