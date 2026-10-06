import Mathlib

open Filter Topology NNReal ENNReal MeasureTheory ProbabilityTheory InnerProductSpace

namespace GradErrors.Stochastic

theorem lemma_2 {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (γ : ℕ → ℝ) (hsq : Summable (fun t => γ t ^ 2))
    (r : ℕ → Ω → F) (B : ℝ)
    (hrm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (r t))
    (hr2 : ∀ t, Integrable (fun ω => ‖r t ω‖ ^ 2) P)
    (hr0 : ∀ t, P[r t | ℱ t] =ᵐ[P] 0)
    (hrB : ∀ t, P[fun ω => ‖r t ω‖ ^ 2 | ℱ t] ≤ᵐ[P] fun _ => B) :
    ∀ᵐ ω ∂P,
      (∃ S : F, Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), γ t • r t ω) atTop (𝓝 S)) ∧
      (∃ S' : ℝ,
        Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), γ t ^ 2 * ‖r t ω‖ ^ 2) atTop (𝓝 S')) := by sorry

end GradErrors.Stochastic

