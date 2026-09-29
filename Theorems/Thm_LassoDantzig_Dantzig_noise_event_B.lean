import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Dantzig

/-- Proof of Lemma B.3 (p. 23): with `r = Aσ√(log M / n)`, the complement of the noise event
`ℬ = ⋂ⱼ {|Vⱼ| ≤ r ‖fⱼ‖_n}`, `Vⱼ = (1/n) ∑ᵢ X i j Wᵢ`, has probability at most `M^{1 − A²/2}`
when the `Wᵢ` are independent `N(0, σ²)`. -/
theorem noise_event_B {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : ∀ j, colNorm X j ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : 0 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    P {ω | ¬ NoiseEvent X r (fun i => W i ω)} ≤
      ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 2)) := by sorry

end LassoDantzig.Dantzig
