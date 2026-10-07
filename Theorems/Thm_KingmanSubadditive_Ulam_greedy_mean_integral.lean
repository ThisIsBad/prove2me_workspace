import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

open MeasureTheory Set

namespace KingmanSubadditive.Ulam

/-- The double integral of the proof of Theorem 8 (Kingman, *Subadditive ergodic theory*, Ann.
Probab. 1(6):883–899 (1973), §2.4, proof of Theorem 8, p. 895):
`∫₀^∞ ∫₀^∞ x e^{−½(x+y)²} dx dy = (π/8)^½`.

**Formalization Note** Only the computation is stated; the paper's claim that this is the mean
of the i.i.d. increments `x_r − x_{r−1}` of a greedy path through a planar Poisson process is not
formalized. The integrand is non-negative and integrable on the quadrant, so the iterated Bochner
integrals are the honest Lebesgue integrals. -/
theorem greedy_mean_integral :
    ∫ y in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), x * Real.exp (-(x + y) ^ 2 / 2) =
      Real.sqrt (Real.pi / 8) := by sorry

end KingmanSubadditive.Ulam

