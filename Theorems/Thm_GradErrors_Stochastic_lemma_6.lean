import Mathlib

open Filter Topology NNReal ENNReal MeasureTheory ProbabilityTheory InnerProductSpace

namespace GradErrors.Stochastic

theorem lemma_6 {n : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hL : LipschitzWith L (gradient f))
    (x s w : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (γ : ℕ → ℝ) (hγ : ∀ t, 0 < γ t)
    (hx : ∀ t ω, x (t + 1) ω = x t ω + γ t • (s t ω + w t ω))
    (hxm : ∀ t, StronglyMeasurable[ℱ t] (x t)) (hsm : ∀ t, StronglyMeasurable[ℱ t] (s t))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h41a : ∀ t ω, c₁ * ‖gradient f (x t ω)‖ ^ 2 ≤ -⟪gradient f (x t ω), s t ω⟫_ℝ)
    (h41b : ∀ t ω, ‖s t ω‖ ≤ c₂ * (1 + ‖gradient f (x t ω)‖))
    (A : ℝ) (hA : 0 < A)
    (h42 : ∀ t (S : Set Ω), MeasurableSet[ℱ t] S → ∫⁻ ω in S, ‖w t ω‖ₑ ∂P < ∞ →
      ∫ ω in S, w t ω ∂P = 0)
    (h43 : ∀ t (S : Set Ω), MeasurableSet[ℱ t] S →
      ∫⁻ ω in S, ‖w t ω‖ₑ ^ 2 ∂P ≤
        ∫⁻ ω in S, ENNReal.ofReal (A * (1 + ‖gradient f (x t ω)‖ ^ 2)) ∂P)
    (hsum : Tendsto (fun T => ∑ t ∈ Finset.range T, γ t) atTop atTop)
    (hsq : Summable (fun t => γ t ^ 2))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᵐ ω ∂P,
      (Tendsto (fun t => f (x t ω)) atTop atBot ∨
        ∃ l : ℝ, Tendsto (fun t => f (x t ω)) atTop (𝓝 l)) ∧
      (¬ Tendsto (fun t => f (x t ω)) atTop atBot →
        ∀ δ' > δ, ∀ᶠ t in atTop, ‖gradient f (x t ω)‖ ≤ δ') := by sorry

end GradErrors.Stochastic

