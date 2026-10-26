import Mathlib.Probability.Kernel.Invariance
import Definitions.Def_SmithHitAndRun_SymMixing_IsSymmetricMixingKernel
import Definitions.Def_SmithHitAndRun_SymMixing_IsClosedSet

open MeasureTheory ProbabilityTheory

namespace SmithHitAndRun.SymMixing

/-- Smith (1984), Lemma 2, p. 1300: no two disjoint nonempty closed sets. -/
theorem lemma_2_indecomposable {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V] (hV : V ≠ 0)
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x) :
    ¬ ∃ A₁ A₂ : Set α,
      IsClosedSet P A₁ ∧ IsClosedSet P A₂ ∧ A₁ ∩ A₂ = ∅ := by sorry

end SmithHitAndRun.SymMixing

