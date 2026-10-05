import Mathlib
import Definitions.Def_DemandResponse_SecondBest_Hamiltonian

namespace DemandResponse.SecondBest

/-- Proposition A.4 (ii), minimiser claim (arXiv:1810.09063v3, p. 30), read in the limit `A ↗ ∞`
(`η_A ≡ 0`) and with the closed interval `[v_x, p v_x / (r+p)]`. Here `y` stands for `v_x` and `k` for
`v_xx`; the objective of (A.11) is `z ↦ F₀(h - k + r z² + p (z - y)²) + μ̄ (z⁻ + y)²`. -/
theorem propA4_ii_minimiser {N d : ℕ} (P : Params N d) (y k : ℝ) :
    let Φ : ℝ → ℝ := fun z =>
      F0 P (P.h - k + P.r * z ^ 2 + P.p * (z - y) ^ 2) + muBar P * (negp z + y) ^ 2
    (0 ≤ y → IsMinOn Φ Set.univ (P.p / (P.r + P.p) * y)) ∧
    (y ≤ 0 → ∃ z ∈ Set.Icc y (P.p / (P.r + P.p) * y), IsMinOn Φ Set.univ z) := by sorry

end DemandResponse.SecondBest

