import Mathlib.Probability.Kernel.Invariance
import Definitions.Def_MarkovIterKernel
import Definitions.Def_SmithHitAndRun_SymMixing_IsSymmetricMixingKernel
import Definitions.Def_SmithHitAndRun_SymMixing_IsClosedSet

open MeasureTheory ProbabilityTheory

namespace SmithHitAndRun.SymMixing

/-- Smith (1984), proof of Theorem 2, step (ii), p. 1301: every n-step chain,
for n at least two, is indecomposable. -/
theorem n_step_indecomposable {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V] (hV : V ≠ 0)
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x) :
    ∀ n : ℕ, 2 ≤ n →
      ¬ ∃ A₁ A₂ : Set α,
        IsClosedSet (MarkovChainCLT.iterKernel P n) A₁ ∧
        IsClosedSet (MarkovChainCLT.iterKernel P n) A₂ ∧ A₁ ∩ A₂ = ∅ := by sorry

end SmithHitAndRun.SymMixing

