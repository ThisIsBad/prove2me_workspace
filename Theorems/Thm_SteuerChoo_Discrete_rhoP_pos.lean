import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

/-- Proof of **Theorem 3.4** (Steuer–Choo 1983, p. 332), first sentence: "By Lemma 3.3 and the
construction of `ρ_p` in (3.6), `ρ_p > 0`." Here `z*` is an ideal criterion vector and `zᵖ ∈ N`. -/
theorem rhoP_pos {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z) :
    0 < rhoP Z zstar zp := by sorry

end SteuerChoo.Discrete
