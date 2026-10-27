import Mathlib
import Definitions.Def_IntractableCoding_Weights_Reductions

namespace IntractableCoding.Weights

open PricingWithTips

/-- For every `x` with `xA = 0` (`A = subspaceMatrix I`), with `x₀ = firstPart I x`,
`x₁ = lastPart I x` and `y = x₀ B`: `|x₁| = |y| + 3n|x₀|` and `|x| = |y| + (3n + 1)|x₀|`. -/
theorem weight_identity (I : ThreeDMInstance)
    (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2)
    (hx : Matrix.vecMul x (subspaceMatrix I) = 0) :
    hammingNorm (lastPart I x) =
        hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) +
          3 * I.1 * hammingNorm (firstPart I x) ∧
      hammingNorm x =
        hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) +
          (3 * I.1 + 1) * hammingNorm (firstPart I x) := by sorry

end IntractableCoding.Weights

