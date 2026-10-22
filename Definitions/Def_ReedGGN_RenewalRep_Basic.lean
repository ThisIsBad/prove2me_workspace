import Mathlib
import Definitions.Def_ReedGGN_Regulator_FluidInput
import Definitions.Def_ReedGGN_Regulator_PathSpace

namespace ReedGGN.RenewalRep

open MeasureTheory Filter Topology

/-- "Locally bounded" on `[0, ∞)` (p. 29): `f` is bounded on every interval `[0, T]`. -/
def IsLocallyBounded (f : ℝ → ℝ) : Prop :=
  ∀ T, 0 ≤ T → ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, |f t| ≤ C

end ReedGGN.RenewalRep
