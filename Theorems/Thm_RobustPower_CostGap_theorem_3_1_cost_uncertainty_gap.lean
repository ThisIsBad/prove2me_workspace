import Mathlib
import Definitions.Def_RobustPower_CostGap_Problems

open MeasureTheory Matrix

namespace RobustPower.CostGap

/-- Theorem 3.1 (p. 22). The instance `n₁ = 0`, `n₂ = n`, `p₂ = 0`, `m = 1`, `c = 0`, `A = 0`,
`B = [1, …, 1]`, `b(ω) = 1`, with uncertainty set `{1} × [0, 1]ⁿ` and the coordinates of `d`
independent and uniform on `[0, 1]`, has `z_Rob(b, d) ≥ (n + 1) · z_Stoch(b, d)`. -/
theorem theorem_3_1_cost_uncertainty_gap {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Fin n → ℝ) (hd : Measurable d) (hrange : Set.range d = Set.Icc 0 1)
    (hlaw : μ.map d = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))) :
    (((n : ℝ) + 1 : ℝ) : EReal) *
        zStochBD μ (0 : Matrix (Fin 1) (Fin 0) ℝ) (fun _ _ => 1 : Matrix (Fin 1) (Fin n) ℝ)
          (fun _ _ => 1 : Ω → Fin 1 → ℝ) (0 : Fin 0 → ℝ) d ∅ ∅ ≤
      zRobBD (0 : Matrix (Fin 1) (Fin 0) ℝ) (fun _ _ => 1 : Matrix (Fin 1) (Fin n) ℝ)
          (fun _ _ => 1 : Ω → Fin 1 → ℝ) (0 : Fin 0 → ℝ) d ∅ ∅ := by sorry

end RobustPower.CostGap

