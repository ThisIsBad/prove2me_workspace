import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

/-- **Theorem 3.4** (Steuer–Choo 1983, p. 332): let `Z` be finite and `zᵖ ∈ N`. Then `zᵖ` uniquely
minimizes the augmented weighted Tchebycheff program (3.5) with the weights `λᵖ` of (b) and `ρ_p` of
(3.6): every other `z^q ∈ Z` has a strictly larger objective value. `z*` is an ideal criterion
vector. -/
theorem theorem_3_4 {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z) :
    ∀ zq ∈ Z, zq ≠ zp →
      augTcheb (lamP zstar zp) (rhoP Z zstar zp) zstar zp <
        augTcheb (lamP zstar zp) (rhoP Z zstar zp) zstar zq := by sorry

end SteuerChoo.Discrete
