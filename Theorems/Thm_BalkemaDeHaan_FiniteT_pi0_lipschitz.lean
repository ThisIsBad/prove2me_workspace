import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0

namespace BalkemaDeHaan.FiniteT

/-- Proof of the Corollary to Theorem 7, p. 802: `|Π_{0,c}(x) - Π_{0,c₀}(x)| ≤ |c - c₀|`
for `c ≥ 0` and all real `c₀` and `x`. -/
theorem pi0_lipschitz (c : ℝ) (hc : 0 ≤ c) (c₀ x : ℝ) :
    |pi0 c x - pi0 c₀ x| ≤ |c - c₀| := by sorry

end BalkemaDeHaan.FiniteT

