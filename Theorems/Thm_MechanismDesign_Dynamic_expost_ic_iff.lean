import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

namespace MechanismDesign.Dynamic

/-- **Proposition 11.3**, p.210. A direct mechanism is incentive-compatible with respect to the
ex post type `θ` if and only if:
(i) for every ex ante type `τ`, `q(τ, θ)` is increasing in `θ`;
(ii) for every ex ante type `τ`, `u(τ, θ)` is absolutely continuous in `θ` on `[θ̲, θ̄]`; it is
differentiable at all but countably many points of `(θ̲, θ̄)`, and wherever it is differentiable
in `θ`, `∂u(τ, θ)/∂θ = q(τ, θ)`;
(iii) for every `τ` and `θ`:
`t(τ, θ) = t(τ, θ̲) + (θ q(τ, θ) − θ̲ q(τ, θ̲)) − ∫_{θ̲}^{θ} q(τ, θ̂) dθ̂`. -/
theorem expost_ic_iff {τlo τhi θlo θhi : ℝ} (m : DirectMechanism τlo τhi θlo θhi) :
    m.IsExPostIC ↔
      (∀ τ ∈ Set.Icc τlo τhi, MonotoneOn (m.q τ) (Set.Icc θlo θhi)) ∧
      (∀ τ ∈ Set.Icc τlo τhi,
        AbsolutelyContinuousOnInterval (m.u τ) θlo θhi ∧
        {θ ∈ Set.Ioo θlo θhi | ¬ DifferentiableAt ℝ (m.u τ) θ}.Countable ∧
        ∀ θ ∈ Set.Ioo θlo θhi, DifferentiableAt ℝ (m.u τ) θ → deriv (m.u τ) θ = m.q τ θ) ∧
      (∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
        m.t τ θ = m.t τ θlo + (θ * m.q τ θ - θlo * m.q τ θlo) - ∫ x in θlo..θ, m.q τ x) := by sorry

end MechanismDesign.Dynamic

