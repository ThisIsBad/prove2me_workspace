import Mathlib
import Definitions.Def_RobustPower_CostGap_Problems

open MeasureTheory Matrix

namespace RobustPower.CostGap

/-- Eq. (3.1), p. 23: in the instance of Theorem 3.1, the policy that buys one unit of a cheapest
coordinate shows `z_Stoch(b, d) ≤ E_μ[min(d₁(ω), …, dₙ(ω))]`. -/
theorem eq_3_1_stoch_le_expected_min {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Fin n → ℝ) (hd : Measurable d) (hrange : Set.range d = Set.Icc 0 1) :
    zStochBD μ (0 : Matrix (Fin 1) (Fin 0) ℝ) (fun _ _ => 1 : Matrix (Fin 1) (Fin n) ℝ)
        (fun _ _ => 1 : Ω → Fin 1 → ℝ) (0 : Fin 0 → ℝ) d ∅ ∅ ≤
      ((∫ ω, (⨅ j, d ω j) ∂μ : ℝ) : EReal) := by sorry

end RobustPower.CostGap

