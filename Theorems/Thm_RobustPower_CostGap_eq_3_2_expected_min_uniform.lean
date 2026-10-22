import Mathlib

open MeasureTheory

namespace RobustPower.CostGap

/-- Eq. (3.2), p. 23: if the coordinates of `d(ω)` are independent and uniform on `[0, 1]`, then
`E_μ[min(d₁(ω), …, dₙ(ω))] = 1/(n + 1)`. -/
theorem eq_3_2_expected_min_uniform {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Fin n → ℝ) (hd : Measurable d)
    (hlaw : μ.map d = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∫ ω, (⨅ j, d ω j) ∂μ = 1 / ((n : ℝ) + 1) := by sorry

end RobustPower.CostGap

