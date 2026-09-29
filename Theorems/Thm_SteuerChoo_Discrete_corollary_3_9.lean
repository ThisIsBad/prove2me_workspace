import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

/-- **Corollary 3.9** (Steuer–Choo 1983, p. 333): with `ρ` of (3.8) in place of `ρ_p`, each
`zᵖ ∈ N` has a `λ̄ ∈ Λ̄` (namely `λᵖ` of (b)) such that `zᵖ` uniquely minimizes the augmented weighted
Tchebycheff program. `Z` is finite and `z*` is an ideal criterion vector. -/
theorem corollary_3_9 {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z) :
    lamP zstar zp ∈ stdSimplex ℝ (Fin k) ∧
      ∀ zq ∈ Z, zq ≠ zp →
        augTcheb (lamP zstar zp) (rho38 Z zstar) zstar zp <
          augTcheb (lamP zstar zp) (rho38 Z zstar) zstar zq := by sorry

end SteuerChoo.Discrete
