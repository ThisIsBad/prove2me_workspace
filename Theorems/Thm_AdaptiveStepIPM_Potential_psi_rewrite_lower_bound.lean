import Mathlib
import Definitions.Def_LinearOptimization_InteriorPointPotential
import Definitions.Def_AdaptiveStepIPM_Potential_Neighborhood

open Matrix

namespace AdaptiveStepIPM.Potential

/-- **§5, p. 11.** For `x, s > 0` the potential (1) can be written as
`ψ(x, s) = (ρ − n) log(xᵀs) − Σⱼ log(x_j s_j/(xᵀs/n)) + n log n`; the sum is nonpositive
(arithmetic–geometric mean inequality), so `ψ(x, s) ≥ (ρ − n) log(xᵀs) + n log n`; hence,
for `ρ > n` and `t ≥ 0`, `ψ(x, s) ≤ −(ρ − n)t + n log n` implies `xᵀs ≤ 2^{−t}`. -/
theorem psi_rewrite_lower_bound {n : ℕ} (hn : 1 ≤ n) (ρ : ℝ) (x s : Fin n → ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j) :
    LinearOptimization.interiorPointPotential ρ x s =
        (ρ - n) * Real.log (x ⬝ᵥ s) -
          ∑ j, Real.log (x j * s j / ((x ⬝ᵥ s) / n)) + n * Real.log n ∧
      (ρ - n) * Real.log (x ⬝ᵥ s) + n * Real.log n ≤
        LinearOptimization.interiorPointPotential ρ x s ∧
      ∀ t : ℝ, (n : ℝ) < ρ → 0 ≤ t →
        LinearOptimization.interiorPointPotential ρ x s ≤ -((ρ - n) * t) + n * Real.log n →
        x ⬝ᵥ s ≤ (2 : ℝ) ^ (-t) := by sorry

end AdaptiveStepIPM.Potential

