import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
import Definitions.Def_ScenarioApproach_Generalization_supportConstraint
import Definitions.Def_ScenarioExact_PartOne_Basic
open MeasureTheory ScenarioApproach.Generalization
open scoped ENNReal

namespace ScenarioExact.PartOne

/-- §3, PART 1, p. 8, sentence after (3.4): `F(α) = α^d` solves (3.4), and it is the only
distribution on `[0, 1]` that does. -/
theorem moment_uniqueness {d : ℕ} (hd : 1 ≤ d) :
    -- existence: the law with density `d α^{d-1}` on `[0, 1]` (distribution function `α^d`) solves (3.4)
    (∀ m : ℕ, d ≤ m →
      (m.choose d : ℝ≥0∞) *
          ∫⁻ α in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - α) ^ (m - d) * ((d : ℝ) * α ^ (d - 1))) =
        1) ∧
    -- uniqueness: every probability law on `[0, 1]` solving (3.4) has distribution function `α^d`
    ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
      (∀ m : ℕ, d ≤ m →
        (m.choose d : ℝ≥0∞) * ∫⁻ α in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - α) ^ (m - d)) ∂μ = 1) →
      ∀ α ∈ Set.Icc (0 : ℝ) 1, μ (Set.Iic α) = ENNReal.ofReal (α ^ d) := by sorry

end ScenarioExact.PartOne

