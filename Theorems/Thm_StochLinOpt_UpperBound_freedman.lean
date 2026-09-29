import Mathlib

open MeasureTheory

namespace StochLinOpt.UpperBound

theorem freedman {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ) (b : ℝ)
    (hmeas : ∀ i ∈ Finset.Icc 1 T, Measurable[𝓕 (i + 1)] (X i))
    (hint : ∀ i ∈ Finset.Icc 1 T, Integrable (X i) P)
    (hint_sq : ∀ i ∈ Finset.Icc 1 T, Integrable (fun ω => X i ω ^ 2) P)
    (hmds : ∀ i ∈ Finset.Icc 1 T, P[X i | 𝓕 i] =ᵐ[P] 0)
    (hb : ∀ i ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, X i ω ≤ b)
    (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    P.real {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω ≤ v} ≤
      Real.exp (-a ^ 2 / (2 * v + 2 * a * b / 3)) := by sorry

end StochLinOpt.UpperBound
