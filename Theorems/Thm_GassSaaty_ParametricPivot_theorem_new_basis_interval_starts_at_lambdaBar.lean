import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization

namespace GassSaaty.ParametricPivot

theorem theorem_new_basis_interval_starts_at_lambdaBar {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (d d' : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i))
    (hnd : ∀ y, IsBasicFeasibleSolution (stdFormSystem A b) y →
      ¬ IsStdDegenerateBasicSolution A b y)
    (B B' : Fin m ↪ Fin n) (x : Fin n → ℝ) (hx : IsSimplexState A b B x)
    (hcons : ∃ t₀ : ℝ, ∀ j, alpha A d B j + t₀ * beta A d' B j ≤ 0)
    (s : Fin n) (hβs : 0 < beta A d' B s)
    (hsmin : ∀ j, 0 < beta A d' B j →
      -alpha A d B s / beta A d' B s ≤ -alpha A d B j / beta A d' B j)
    (ℓ : Fin m) (hℓ : 0 < pivotColumn A B s ℓ)
    (hratio : ∀ i, 0 < pivotColumn A B s i →
      x (B ℓ) / pivotColumn A B s ℓ ≤ x (B i) / pivotColumn A B s i)
    (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i) :
    IsLeast
      {t : ℝ | IsLpOptimal (d + t • d') (stdPolyhedron A b)
        (x + (x (B ℓ) / pivotColumn A B s ℓ) • basicDirection A B s)}
      (-alpha A d B s / beta A d' B s) := by sorry

end GassSaaty.ParametricPivot

