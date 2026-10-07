import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

namespace KingmanSubadditive.Ulam

/-- The optimisation at the end of the proof of Theorem 8 (Kingman, *Subadditive ergodic theory*,
Ann. Probab. 1(6):883–899 (1973), §2.4, p. 896): the infimum of the values `b > 0` for which some
`α ∈ (0, b)` satisfies (2.4.8), `2α + (b − α) log (b − α) − α log α − b log b < 0`, is
`β = δ^½ + δ^{−½}`, where `δ` is the unique positive root of `log (1 + δ) = 2δ/(1 + δ)`.

**Formalization Note** The first conjunct asserts that the positive root exists and is unique,
so the second is not vacuous. The set of admissible `b` is nonempty and bounded below by `0`, so
the real `sInf` is the true infimum. -/
theorem beta_infimum :
    (∃! δ : ℝ, 0 < δ ∧ Real.log (1 + δ) = 2 * δ / (1 + δ)) ∧
    ∀ δ : ℝ, 0 < δ → Real.log (1 + δ) = 2 * δ / (1 + δ) →
      sInf {b : ℝ | 0 < b ∧ ∃ α : ℝ, 0 < α ∧ α < b ∧ stirlingExponent α b < 0} =
        Real.sqrt δ + 1 / Real.sqrt δ := by sorry

end KingmanSubadditive.Ulam

