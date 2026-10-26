import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation

namespace ReedGGN.Regulator

open MeasureTheory

/-- Proof of Proposition 3.1, Uniqueness (p. 34): if `B(y + δ) − B(y) < ε` for all `y ≥ 0`
(and the first window `[0, δ]`, atom at `0` included, has mass `< ε`), with `0 < ε < 1`,
then two càdlàg solutions of (3.1) for the same càdlàg input agree on `[0, ∞)`. -/
theorem uniqueness (μ : Measure ℝ) [IsProbabilityMeasure μ] (a δ ε : ℝ)
    (hδ : 0 < δ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hB₀ : μ (Set.Icc 0 δ) < ENNReal.ofReal ε)
    (hB : ∀ y, 0 ≤ y → μ (Set.Ioc y (y + δ)) < ENNReal.ofReal ε)
    (x u v : ℝ → ℝ) (hx : IsCadlag x) (hu : IsCadlag u) (hv : IsCadlag v)
    (hsu : SolvesRegulator μ a x u) (hsv : SolvesRegulator μ a x v) :
    Set.EqOn u v (Set.Ici 0) := by sorry

end ReedGGN.Regulator

