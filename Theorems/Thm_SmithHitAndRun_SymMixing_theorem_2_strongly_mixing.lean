import Mathlib.Probability.Kernel.Invariance
import Definitions.Def_MarkovIterKernel
import Definitions.Def_SmithHitAndRun_SymMixing_uniformLaw
import Definitions.Def_SmithHitAndRun_SymMixing_IsSymmetricMixingKernel

open MeasureTheory ProbabilityTheory Filter

namespace SmithHitAndRun.SymMixing

/-- Smith (1984), Theorem 2, p. 1301: setwise convergence from every start. -/
theorem theorem_2_strongly_mixing {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V] (hV : V ≠ 0)
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x) :
    ∀ x : α, ∀ A : Set α, MeasurableSet A →
      Tendsto (fun m : ℕ => MarkovChainCLT.iterKernel P m x A)
        atTop (nhds (uniformLaw V A)) := by sorry

end SmithHitAndRun.SymMixing

