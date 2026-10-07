import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0

namespace BalkemaDeHaan.FiniteT

/-- Lemma 4, p. 802: `0 ≤ -(∂/∂c) Π_{0,c}(x) < 1` for `c > -1` if `x ≠ 0` and `c x ≠ -1`;
in particular `c ↦ Π_{0,c}(x)` is differentiable at such `c`. -/
theorem lemma_4 (c x : ℝ) (hc : -1 < c) (hx : x ≠ 0) (hcx : c * x ≠ -1) :
    ∃ d : ℝ, HasDerivAt (fun c' : ℝ => pi0 c' x) d c ∧ 0 ≤ -d ∧ -d < 1 := by sorry

end BalkemaDeHaan.FiniteT

