import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

namespace MechanismDesign.Dynamic

/-- **Proposition 11.1 (Dynamic Revelation Principle)**, p.207. For every (reduced-form) dynamic
mechanism `Γ` and every optimal buyer strategy `σ = (σ₁, σ₂)` in `Γ`, there is a direct
mechanism `Γ′ = (q, t)` and an optimal buyer strategy `σ′ = (σ′₁, σ′₂)` in `Γ′` such that
(i) `σ′₁(τ) = τ` for every `τ ∈ [τ̲, τ̄]` and `σ′₂(τ, θ, τ) = θ` for every `θ ∈ [θ̲, θ̄]`,
`τ ∈ [τ̲, τ̄]`; and (ii) for every `(τ, θ) ∈ [τ̲, τ̄] × [θ̲, θ̄]`, `q(τ, θ)` and `t(τ, θ)` equal
the probability of purchase and the expected payment that result under `Γ` when the buyer
plays `σ`. -/
theorem dynamic_revelation_principle {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (Γ : DynMechanism) (hΓ : Γ.Valid) (σ₁ : ℝ → Γ.A₁) (σ₂ : ℝ → ℝ → Γ.A₁ → Γ.A₂)
    (hσ : Γ.IsOptimalStrategy E σ₁ σ₂) :
    ∃ (m : DirectMechanism τlo τhi θlo θhi) (σ₁' : ℝ → Set.Icc τlo τhi)
      (σ₂' : ℝ → ℝ → Set.Icc τlo τhi → Set.Icc θlo θhi),
      m.toDyn.IsOptimalStrategy E σ₁' σ₂' ∧
      (∀ τ ∈ Set.Icc τlo τhi, (σ₁' τ : ℝ) = τ) ∧
      (∀ τ (hτ : τ ∈ Set.Icc τlo τhi), ∀ θ ∈ Set.Icc θlo θhi, (σ₂' τ θ ⟨τ, hτ⟩ : ℝ) = θ) ∧
      (∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
        m.q τ θ = Γ.prob (σ₁ τ) (σ₂ τ θ (σ₁ τ)) ∧ m.t τ θ = Γ.pay (σ₁ τ) (σ₂ τ θ (σ₁ τ))) := by sorry

end MechanismDesign.Dynamic

