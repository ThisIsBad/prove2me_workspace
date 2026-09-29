import Mathlib

open MeasureTheory

namespace StochLinOpt.LowerBound

theorem freedman {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ) (b : ℝ)
    (hmeas : ∀ i ∈ Finset.Icc 1 T, Measurable[ℱ i] (X i))
    (hint : ∀ i ∈ Finset.Icc 1 T, Integrable (X i) P)
    (hint_sq : ∀ i ∈ Finset.Icc 1 T, Integrable (fun ω => X i ω ^ 2) P)
    (hmds : ∀ i ∈ Finset.Icc 1 T, P[X i | ℱ (i - 1)] =ᵐ[P] 0)
    (hb : ∀ i ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, X i ω ≤ b)
    (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    P.real {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | ℱ (i - 1)] ω ≤ v} ≤
      Real.exp (-a ^ 2 / (2 * v + 2 * a * b / 3)) := by sorry

end StochLinOpt.LowerBound

