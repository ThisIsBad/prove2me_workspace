import Mathlib
import Definitions.Def_KingmanSubadditive_BanachAlgebra_Process

namespace KingmanSubadditive.BanachAlgebra

open MeasureTheory

/-- **Proof of Theorem 2, §1.2, p. 886** (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973), DOI 10.1214/aop/1176996798). "It is trivial to check that `x^(N)` is a
subadditive process, where `x_st^(N) = max(x_st, −N(t − s))` and `N` is any positive integer."
The hypotheses are those of Theorem 2 that the truncation uses: `x` is a measurable family of real
random variables satisfying S₁, S₂ and S₃′.

**Formalization Note.** "Subadditive process" is `IsSubadditiveProcess`: measurability, S₁
(almost surely, for each triple), S₂ (joint-law stationarity of the whole path) and S₃
(integrable `x_0t^(N)` with a linear lower bound on the means). -/
theorem truncation_isSubadditive {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : IsMeasurableFamily x) (h1 : S1 P x) (h2 : S2 P x) (h3' : S3' P x)
    (N : ℕ) (hN : 1 ≤ N) :
    IsSubadditiveProcess P (truncate x N) := by sorry

end KingmanSubadditive.BanachAlgebra

