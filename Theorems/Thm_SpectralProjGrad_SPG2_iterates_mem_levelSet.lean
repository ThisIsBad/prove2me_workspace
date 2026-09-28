import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_SpectralProjGrad_SPG2_IsSPG2Run

namespace SpectralProjGrad.SPG2

/-- Section 2, p. 4: the line search condition (3) guarantees that the SPG2 iterates remain in
`Ω₀ = {x ∈ Ω : f(x) ≤ f(x₀)}`. -/
theorem iterates_mem_levelSet {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {M : ℕ} {αmin αmax γ σ₁ σ₂ : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hM : 1 ≤ M) (hαmin : 0 < αmin) (hαmin_lt : αmin < αmax)
    (hγ : γ ∈ Set.Ioo 0 1) (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) (hσ₂ : σ₂ < 1)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {α : ℕ → ℝ}
    (hrun : IsSPG2Run Ω f P M αmin αmax γ σ₁ σ₂ x α) :
    ∀ k, x k ∈ {y ∈ Ω | f y ≤ f (x 0)} := by sorry

end SpectralProjGrad.SPG2

