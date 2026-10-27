import Mathlib
import Definitions.Def_IntractableCoding_Weights_Reductions

namespace IntractableCoding.Weights

open PricingWithTips

/-- For every `x` with `xA = 0` (`A = subspaceMatrix I`, `n = |T|`), with `x₀ = firstPart I x`
and `y = x₀ B`: `|y| ≤ 3n`, `|x₀|` is the quotient and `|y|` the remainder of `|x|` divided by
`3n + 1`, and if `|x| = 3n² + 4n` then `|x₀| = n` and `|y| = 3n`. -/
theorem weight_quotient_remainder (I : ThreeDMInstance)
    (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2)
    (hx : Matrix.vecMul x (subspaceMatrix I) = 0) :
    hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) ≤ 3 * I.1 ∧
      hammingNorm (firstPart I x) = hammingNorm x / (3 * I.1 + 1) ∧
      hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) = hammingNorm x % (3 * I.1 + 1) ∧
      (hammingNorm x = 3 * I.1 ^ 2 + 4 * I.1 →
        hammingNorm (firstPart I x) = I.1 ∧
          hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) = 3 * I.1) := by sorry

end IntractableCoding.Weights

