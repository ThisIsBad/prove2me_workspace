import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model
import Definitions.Def_MechanismDesign_Dynamic_OptimalScreening

namespace MechanismDesign.Dynamic

/-- **Proposition 11.5**, p.214. If an (admissible) direct mechanism is incentive-compatible, then
for all `(τ, θ) ∈ [τ̲, τ̄] × [θ̲, θ̄]`
`t(τ, θ) = t₀(τ) + θ q(τ, θ) − ∫_{θ̲}^{θ} q(τ, θ̂) dθ̂`, where
`t₀(τ) = t(τ̲, θ̲) − θ̲ q(τ̲, θ̲) + ∫_{τ̲}^{τ} ∫_{θ̲}^{θ̄} q(τ̂, θ̂) ∂F(θ̂|τ̂)/∂τ dθ̂ dτ̂
  + ∫_{θ̲}^{θ̄} ∫_{θ̲}^{θ̂} [q(τ, x) f(θ̂|τ) − q(τ̲, x) f(θ̂|τ̲)] dx dθ̂` (`SeqEnv.t0`). -/
theorem transfer_formula {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (m : DirectMechanism τlo τhi θlo θhi) (hm : m.Admissible) (hic : m.IsIC E) :
    ∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
      m.t τ θ = E.t0 m.q (m.t τlo θlo) τ + θ * m.q τ θ - ∫ x in θlo..θ, m.q τ x := by sorry

end MechanismDesign.Dynamic

