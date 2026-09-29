import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

/-- **Theorem 3.7** (Steuer–Choo 1983, p. 332): let `Z` be finite, `z*` an ideal criterion vector
and `ρ` as in (3.8). Then for `zᵖ ∈ Z`: `zᵖ ∈ N` if and only if there exists `λ ∈ Λ̄` such that `zᵖ`
minimizes the augmented weighted Tchebycheff program over `Z`. -/
theorem nondominated_iff_augmented_minimizer {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ))
    (zstar : Fin k → ℝ) (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hzp : zp ∈ Z) :
    zp ∈ nondominated Z ↔
      ∃ lam ∈ stdSimplex ℝ (Fin k),
        ∀ z ∈ Z, augTcheb lam (rho38 Z zstar) zstar zp ≤ augTcheb lam (rho38 Z zstar) zstar z := by sorry

end SteuerChoo.Discrete
