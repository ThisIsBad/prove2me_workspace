import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_IsPhiDivergenceFunction
import Definitions.Def_PhiDivRobust_Counterpart_conj
import Definitions.Def_PhiDivRobust_Counterpart_scaledConj
import Definitions.Def_PhiDivRobust_Counterpart_perspConj
open Matrix

namespace PhiDivRobust.Counterpart

/-- Ben-Tal et al. 2013, p. 347, proof of Theorem 1, closing paragraph: `(λφ)*(s) = λ φ*(s/λ)` for
`λ ≥ 0`, where `0 φ*(s/0) := (0φ)*(s)`, which equals `0` if `s ≤ 0` and `+∞` if `s > 0`. -/
theorem scaledConj_eq_perspConj (φ : ℝ → EReal) (hφ : IsPhiDivergenceFunction φ)
    (lam s : ℝ) (hlam : 0 ≤ lam) :
    scaledConj φ lam s = perspConj φ lam s := by sorry

end PhiDivRobust.Counterpart
