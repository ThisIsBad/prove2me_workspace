import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto

namespace SpectralProjGrad.SPG1

/-- Theorem 2.2, first clause (SPG1 is well defined), in single-iteration form: at a point
`x ∈ Ω` where Step 1 does not stop (`‖P(x - g(x)) - x‖ ≠ 0`), with `α ∈ [α_min, α_max]` and any
reference value `R ≥ f(x)`, every backtracking sequence `μ_0 = α`, `μ_{i+1} ∈ [σ₁ μ_i, σ₂ μ_i]`
reaches a trial point `x₊ = P(x - μ_i g(x))` satisfying the nonmonotone Armijo test (1)
along the projection arc: `f(x₊) ≤ R + γ ⟨x₊ - x, g(x)⟩`. -/
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
    (μ : ℕ → ℝ) (hμ0 : μ 0 = α)
    (hμ : ∀ i, σ₁ * μ i ≤ μ (i + 1) ∧ μ (i + 1) ≤ σ₂ * μ i) :
    ∃ i, f (P (x - μ i • gradient f x)) ≤
      R + γ * inner ℝ (P (x - μ i • gradient f x) - x) (gradient f x) := by sorry

end SpectralProjGrad.SPG1

