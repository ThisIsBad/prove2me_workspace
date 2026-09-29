import Mathlib
import Definitions.Def_CaiCandesShen_GeneralConvex_Problem
open Filter Topology

namespace CaiCandesShen.GeneralConvex

/-- Theorem 4.4, p. 1969: let `f_1, …, f_m` be convex, let `𝓕 = (f_1, …, f_m)` obey the
Lipschitz bound (4.2) with constant `L ≥ 0`, and suppose the step sizes obey
`0 < inf δ_k ≤ sup δ_k < 2 / L²` (stated as `a ≤ δ_k ≤ C` for `k ≥ 1` with `a > 0` and
`C L² < 2`). Assuming strong duality (a primal-dual optimal pair of (3.4) exists), the sequence
`X^k` obtained via (3.5) from `y⁰ = 0` converges to the unique solution of (3.4). -/
theorem svt_general_converges {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (f : Fin m → Mat n₁ n₂ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ X Y : Mat n₁ n₂, eucNorm (constraintMap f X - constraintMap f Y) ≤ L * frobNorm (X - Y))
    (hdual : ∃ (Xs : Mat n₁ n₂) (ys : Fin m → ℝ), IsPrimalDualOptimal τ f Xs ys)
    (δ : ℕ → ℝ)
    (hδ : ∃ a C : ℝ, 0 < a ∧ C * L ^ 2 < 2 ∧ ∀ k : ℕ, 1 ≤ k → a ≤ δ k ∧ δ k ≤ C)
    (X : ℕ → Mat n₁ n₂) (y : ℕ → Fin m → ℝ) (hseq : IsGeneralSVTSeq τ f δ X y) :
    (∃! Xs : Mat n₁ n₂, IsSol34 τ f Xs) ∧
      ∀ Xs : Mat n₁ n₂, IsSol34 τ f Xs → Tendsto X atTop (𝓝 Xs) := by sorry

end CaiCandesShen.GeneralConvex
