import Mathlib
import Definitions.Def_ReedGGN_RenewalRep_Basic
import Definitions.Def_ReedGGN_RenewalRep_RenewalFunction
import Definitions.Def_ReedGGN_RenewalRep_Equations

namespace ReedGGN.RenewalRep

open MeasureTheory

/-- Corollary 5.2, p. 29, pathwise. For a service law `μ` (probability measure on `[0, ∞)` with
mean `1`), every càdlàg driving path `ζ` and every `β ∈ ℝ`:
1. a càdlàg path solves the limit equation (5.33) if and only if it solves the renewal-function
   equation (5.41);
2. (5.41) has a càdlàg solution, unique on `[0, ∞)` among càdlàg paths. -/
theorem corollary_5_2 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hint : Integrable id μ) (hmean : ∫ x, x ∂μ = 1)
    (ζ : ℝ → ℝ) (hζ : ReedGGN.Regulator.IsCadlag ζ) (β : ℝ) :
    (∀ q : ℝ → ℝ, ReedGGN.Regulator.IsCadlag q → (SolvesLimitEq μ ζ β q ↔ SolvesRenewalEq μ ζ β q)) ∧
    ∃ q : ℝ → ℝ, ReedGGN.Regulator.IsCadlag q ∧ SolvesRenewalEq μ ζ β q ∧
      ∀ q' : ℝ → ℝ, ReedGGN.Regulator.IsCadlag q' → SolvesRenewalEq μ ζ β q' → Set.EqOn q' q (Set.Ici 0) := by sorry

end ReedGGN.RenewalRep

