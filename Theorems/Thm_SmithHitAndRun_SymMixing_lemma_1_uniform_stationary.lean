import Mathlib.Probability.Kernel.Invariance
import Definitions.Def_SmithHitAndRun_SymMixing_uniformLaw
import Definitions.Def_SmithHitAndRun_SymMixing_IsSymmetricMixingKernel

open MeasureTheory ProbabilityTheory Filter

namespace SmithHitAndRun.SymMixing

/-- Smith (1984), Lemma 1, p. 1300: the uniform law is stationary. -/
theorem lemma_1_uniform_stationary {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V] (hV : V ≠ 0)
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) :
    ∀ A : Set α, MeasurableSet A →
      uniformLaw V A = ∫⁻ x, P x A ∂(uniformLaw V) := by sorry

end SmithHitAndRun.SymMixing

