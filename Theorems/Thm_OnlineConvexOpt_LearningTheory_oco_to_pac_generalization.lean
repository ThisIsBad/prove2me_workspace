import Mathlib
import Definitions.Def_OnlineConvexOpt_LearningTheory_GeneralizationError
import Definitions.Def_OnlineConvexOpt_LearningTheory_AgnosticReduction
import Definitions.Def_OnlineConvexOpt_FirstOrder_Algorithm
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open MeasureTheory

namespace OnlineConvexOpt.LearningTheory

/-- Theorem 9.5 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 158, PDF p. 180). Let `A` be an OCO algorithm whose regret after `T`
iterations is guaranteed to be bounded by `RegretT(A)`. Then for any `δ > 0`, with probability
at least `1 − δ`, it holds that
`error(h̄) ≤ error(h⋆) + Regret_T(A)/T + √(8 log(2/δ)/T)`.

`h̄` is Algorithm 29's output (`IsAgnosticReductionRun`), `h⋆ = arg min_{h∈H}{error(h)}`
(p. 158). `A`'s regret guarantee is stated as `hA`, reusing the published
`OnlineConvexOpt.FirstOrder.RegretT` (Chunk 03): for every cost sequence and every horizon, `A`'s
regret against the best fixed hypothesis in `H` is at most `RegretBoundA T` — the hypothesis "an
OCO algorithm whose regret is guaranteed to be bounded by `RegretT(A)`" made explicit as a
property of `A` (not a one-off fact about the realized random cost sequence). `hAnonant`, reusing
the published `OnlineConvexOpt.FirstOrder.IsOnlineAlgorithm` (Chunk 03), requires `A` to be
non-anticipating and to play inside `H`: without it, `hA`'s universal regret guarantee over an
arbitrary cost sequence says nothing about the specific plays `IsAgnosticReductionRun`'s `h`
produces from truncated cost sequences, since those truncations agree with the real realized
sequence only on rounds strictly before the one being played. Measurability hypotheses
(`hpred`, `hℓmeas`, `hhbar`) guard `GeneralizationError`'s integral and the final probability
event against silently collapsing to Mathlib's junk value on a non-measurable input. -/
theorem oco_to_pac_generalization
    {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (D : Measure (X × Y)) [IsProbabilityMeasure D]
    (H : Set E) (pred : E → X → ℝ) (ℓ : ℝ → Y → ℝ)
    (hℓbdd : ∀ yhat y, 0 ≤ ℓ yhat y ∧ ℓ yhat y ≤ 1)
    (hpred : Measurable (Function.uncurry pred))
    (hℓmeas : Measurable (Function.uncurry ℓ))
    (A : (ℕ → E → ℝ) → ℕ → E)
    (hAnonant : OnlineConvexOpt.FirstOrder.IsOnlineAlgorithm H A)
    (RegretBoundA : ℕ → ℝ)
    (hA : ∀ (T : ℕ) (f : ℕ → E → ℝ), 1 ≤ T →
      OnlineConvexOpt.FirstOrder.RegretT H f (A f) T ≤ RegretBoundA T)
    (T : ℕ) (hT : 1 ≤ T)
    (samp : ℕ → Ω → X × Y) (h : ℕ → Ω → E) (hbar : Ω → E)
    (hrun : IsAgnosticReductionRun Prob D pred ℓ A T samp h hbar)
    (hhbar : Measurable hbar)
    (hstar : E) (hstar_mem : hstar ∈ H)
    (hstar_min : ∀ y ∈ H, GeneralizationError D pred ℓ hstar ≤ GeneralizationError D pred ℓ y)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ) ≤
      (Prob {ω | GeneralizationError D pred ℓ (hbar ω) ≤
        GeneralizationError D pred ℓ hstar + RegretBoundA T / T +
          Real.sqrt (8 * Real.log (2 / δ) / T)}).toReal := by sorry

end OnlineConvexOpt.LearningTheory
