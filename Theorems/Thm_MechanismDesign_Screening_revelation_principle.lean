import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Proposition 2.1 (Revelation Principle)**, p.10. For every (reduced-form) selling mechanism
`Γ` and every optimal buyer strategy `σ` in `Γ`, there is a direct mechanism `Γ′ = (q, t)` and an
optimal buyer strategy `σ′` in `Γ′` such that (i) `σ′(θ) = θ` for every `θ ∈ [θ̲, θ̄]`, and
(ii) for every `θ ∈ [θ̲, θ̄]`, `q(θ)` and `t(θ)` equal the probability of purchase and the expected
payment that result under `Γ` when the buyer plays `σ`. -/
theorem revelation_principle {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (Γ : Mechanism) (σ : ℝ → Γ.S) (hσ : Γ.IsOptimalStrategy θlo θhi σ) :
    ∃ (m : DirectMechanism θlo θhi) (σ' : ℝ → ℝ), m.IsOptimalStrategy σ' ∧
      (∀ θ ∈ Set.Icc θlo θhi, σ' θ = θ) ∧
      (∀ θ ∈ Set.Icc θlo θhi, m.q θ = Γ.prob (σ θ) ∧ m.t θ = Γ.pay (σ θ)) := by sorry

end MechanismDesign.Screening

