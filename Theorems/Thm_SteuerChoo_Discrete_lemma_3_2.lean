import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

/-- **Lemma 3.2** (Steuer–Choo 1983, p. 331), corrected: under (a)–(c), with `z*` an ideal
criterion vector, `zᵖ ∈ N`, `z^q ∈ Z`, `z^q ≠ zᵖ` and `z^q ≰ zᵖ`, the vector `z^q` does not lie in
`Φ(α_pp)` for the weights `λᵖ` of (b). The printed lemma omits `z^q ≰ zᵖ` and is false without it. -/
theorem lemma_3_2 {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z)
    (zq : Fin k → ℝ) (hq : zq ∈ Z) (hne : zq ≠ zp) (hnle : ¬ zq ≤ zp) :
    zq ∉ Phi (lamP zstar zp) zstar (alphaPQ zstar zp zp) := by sorry

end SteuerChoo.Discrete
