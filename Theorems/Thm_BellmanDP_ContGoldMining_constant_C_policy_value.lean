import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process

namespace BellmanDP.ContGoldMining

/-- Bellman, *Dynamic Programming*, Ch. VIII, § 15, proof of Lemma 6, Eq. (1), p. 237, corrected:
using `C` for all `t ≥ 0` yields `f_C(∞) = r₃ x₀/(q₃ + r₃) + r₄ y₀/(q₃ + r₄)`
(the print has `q₂ + r₃` in the first denominator). -/
theorem constant_C_policy_value (P : Params) (hP : P.Positive) (x₀ y₀ : ℝ) (hx₀ : 0 ≤ x₀)
    (hy₀ : 0 ≤ y₀) :
    goldInfty P x₀ y₀ (fun i _ => ![0, 0, 1] i) =
      ENNReal.ofReal (P.r₃ * x₀ / (P.q₃ + P.r₃) + P.r₄ * y₀ / (P.q₃ + P.r₄)) := by sorry

end BellmanDP.ContGoldMining

