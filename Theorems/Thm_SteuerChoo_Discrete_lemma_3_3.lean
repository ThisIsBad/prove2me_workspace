import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

/-- **Lemma 3.3** (Steuer–Choo 1983, p. 331), corrected: under (a)–(d), with `z*` an ideal
criterion vector, `zᵖ ∈ N`, `z^q ∈ Z`, `z^q ≠ zᵖ` and `z^q ≰ zᵖ`, we have `α_pp < α_pq`. The printed
lemma omits `z^q ≰ zᵖ` and is false without it. -/
theorem lemma_3_3 {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z)
    (zq : Fin k → ℝ) (hq : zq ∈ Z) (hne : zq ≠ zp) (hnle : ¬ zq ≤ zp) :
    alphaPQ zstar zp zp < alphaPQ zstar zp zq := by sorry

end SteuerChoo.Discrete
