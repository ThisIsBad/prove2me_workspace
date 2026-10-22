import Mathlib
import Definitions.Def_LeviBalancing_DualBalancing_Model
import Definitions.Def_LeviBalancing_DualBalancing_Policy
open Finset MeasureTheory
open scoped ENNReal

namespace LeviBalancing.DualBalancing

/-- Lemma 4.1, p. 294: the expected cost of a dual-balancing policy is twice the expected sum of
the balanced costs `Z_t = E[H_t^B | ℱ t] = E[Π_t^B | ℱ t]`, `t = 1, …, T − L`. -/
theorem expected_cost_eq_two_sum_balanced {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℤ m} (I : Instance) (dem : DemandProcess ℱ μ I.T)
    (B : ℤ → Ω → ℝ) (hB : IsDualBalancing I ℱ μ dem.D B) :
    expectedCost I μ dem.D B =
      2 * ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L),
        ∫⁻ ω, ENNReal.ofReal ((μ[randHolding I dem.D B t | ℱ t]) ω) ∂μ := by sorry

end LeviBalancing.DualBalancing

