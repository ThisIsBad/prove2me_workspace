import Mathlib
import Definitions.Def_KingmanSubadditive_BanachAlgebra_Process

namespace KingmanSubadditive.BanachAlgebra

open MeasureTheory

/-- **(1.2.7), §1.2, p. 885** (Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899
(1973), DOI 10.1214/aop/1176996798). "Note that by (1.1.1) this implies that `E(x_st⁺) < ∞` for
all `s < t`": if a measurable family of real random variables satisfies S₁, S₂ and S₃′
(`E(x₀₁⁺) < ∞`), then `E(x_st⁺) < ∞` for every `s < t`.

**Formalization Note.** The positive part `x⁺ = max(x, 0)` is integrated as a lower Lebesgue
integral of `ENNReal.ofReal`. S₂ (joint-law stationarity) is among the hypotheses because it is
what transports `E(x₀₁⁺) < ∞` to `E(x_{r,r+1}⁺) < ∞`; S₃ is not assumed. -/
theorem positive_part_finite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : IsMeasurableFamily x) (h1 : S1 P x) (h2 : S2 P x) (h3' : S3' P x) :
    ∀ s t : ℕ, s < t → ∫⁻ ω, ENNReal.ofReal (x s t ω) ∂P < ⊤ := by sorry

end KingmanSubadditive.BanachAlgebra

