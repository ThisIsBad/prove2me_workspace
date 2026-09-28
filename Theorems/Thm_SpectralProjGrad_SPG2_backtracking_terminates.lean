import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_SpectralProjGrad_Shared_scaledProjGrad

namespace SpectralProjGrad.SPG2

/-- Theorem 2.1, first clause (SPG2 is well defined), in single-iteration form: at a point
`x ∈ Ω` where Step 1 does not stop (`‖P(x - g(x)) - x‖ ≠ 0`), with `α ∈ [α_min, α_max]`,
`d = P(x - α g(x)) - x` and any reference value `R ≥ f(x)`, every backtracking sequence
`μ_0 = 1`, `μ_{i+1} ∈ [σ₁ μ_i, σ₂ μ_i]` reaches a trial step satisfying the nonmonotone
Armijo test `f(x + μ_i d) ≤ R + γ μ_i ⟨d, g(x)⟩`. -/
theorem backtracking_terminates {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {αmin αmax γ σ₁ σ₂ : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hαmin : 0 < αmin) (hαmin_lt : αmin < αmax)
    (hγ : γ ∈ Set.Ioo 0 1) (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) (hσ₂ : σ₂ < 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (hstep1 : ‖P (x - gradient f x) - x‖ ≠ 0)
    (α : ℝ) (hα : α ∈ Set.Icc αmin αmax)
    (R : ℝ) (hR : f x ≤ R)
    (μ : ℕ → ℝ) (hμ0 : μ 0 = 1)
    (hμ : ∀ i, σ₁ * μ i ≤ μ (i + 1) ∧ μ (i + 1) ≤ σ₂ * μ i) :
    ∃ i, f (x + μ i • SpectralProjGrad.Shared.scaledProjGrad P f α x) ≤
      R + γ * μ i * inner ℝ (SpectralProjGrad.Shared.scaledProjGrad P f α x) (gradient f x) := by sorry

end SpectralProjGrad.SPG2

