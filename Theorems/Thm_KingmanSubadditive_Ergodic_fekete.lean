import Mathlib
import Definitions.Def_KingmanSubadditive_Ergodic_Process

namespace KingmanSubadditive.Ergodic

open MeasureTheory Filter Topology

/-- Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973),
p. 883, (1.1.4)–(1.1.5). As on the page, the hypotheses are S₁, S₃ and only
the one-dimensional stationarity S₂′ ("the distribution of `x_st` depends only
on `t − s`"), written as equality of the law of `x_st` with that of
`x_{0,t−s}` for every `s < t` (the natural-number subtraction is never
truncated there). Measurability of each valid coordinate is the paper's
"random variables". The infimum `gamma` excludes `t = 0`. -/
theorem fekete {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ s t : ℕ, s < t → Measurable (x s t))
    (hS1 : S1 x)
    (hS2' : ∀ s t : ℕ, s < t → Measure.map (x s t) P = Measure.map (x 0 (t - s)) P)
    (hS3 : S3 P x) :
    Tendsto (fun t : ℕ => mean P x t / (t : ℝ)) atTop (𝓝 (gamma P x)) := by sorry

end KingmanSubadditive.Ergodic

