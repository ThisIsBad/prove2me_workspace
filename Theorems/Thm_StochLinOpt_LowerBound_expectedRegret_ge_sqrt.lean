import Mathlib
import Definitions.Def_StochLinOpt_LowerBound_circleBandit

open MeasureTheory

namespace StochLinOpt.LowerBound

theorem expectedRegret_ge_sqrt :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S : Type) [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]
        (π : RandomizedPolicy S) (T : ℕ), 1 ≤ T →
        c * Real.sqrt T ≤ expectedRegret ρ π T := by sorry

end StochLinOpt.LowerBound

