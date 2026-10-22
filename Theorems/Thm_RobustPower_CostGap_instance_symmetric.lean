import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets

open MeasureTheory

namespace RobustPower.CostGap

/-- Proof of Theorem 3.1, pp. 22–23: the uncertainty set `{(b(ω), d(ω))} = {1} × [0, 1]ⁿ` is
symmetric about `(1, (1/2, …, 1/2))`, and `E_μ[d(ω)] = (1/2, …, 1/2)`, so (2.1) holds. -/
theorem instance_symmetric {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Fin n → ℝ) (hd : Measurable d) (hrange : Set.range d = Set.Icc 0 1)
    (hlaw : μ.map d = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))) :
    RobustPower.StochGap.IsSymmetricAbout (Set.range fun ω => ((fun _ => 1 : Fin 1 → ℝ), d ω))
        ((fun _ => 1 : Fin 1 → ℝ), (fun _ => 1 / 2 : Fin n → ℝ)) ∧
      ∫ ω, d ω ∂μ = (fun _ => 1 / 2 : Fin n → ℝ) := by sorry

end RobustPower.CostGap

