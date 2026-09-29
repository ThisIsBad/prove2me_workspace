import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Equivalence

/-- (B.4): the complement of the noise event `𝒜 = ⋂ⱼ {2|Vⱼ| ≤ r‖fⱼ‖_n}` has probability at most
`M^{1 − A²/8}` when `r = Aσ√(log M / n)`. -/
theorem eq_B4_noise_event {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : ∀ j, colNorm X j ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : 0 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    P {ω | ¬ NoiseEventHalf X r (fun i => W i ω)} ≤
      ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 8)) := by sorry

end LassoDantzig.Equivalence
