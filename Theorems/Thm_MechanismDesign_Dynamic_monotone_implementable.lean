import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

namespace MechanismDesign.Dynamic

/-- **Proposition 11.6**, p.215. If `q(τ, θ)` (with values in `[0, 1]`, measurable) is
increasing in `τ` and in `θ`, then there exists a (measurable) transfer schedule `t(τ, θ)` such
that the direct mechanism `(q, t)` is incentive-compatible. -/
theorem monotone_implementable {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (q : ℝ → ℝ → ℝ)
    (hq : ∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi, q τ θ ∈ Set.Icc (0 : ℝ) 1)
    (hqm : Measurable (fun p : Set.Icc τlo τhi × Set.Icc θlo θhi => q p.1 p.2))
    (hτ : ∀ θ ∈ Set.Icc θlo θhi, MonotoneOn (fun τ => q τ θ) (Set.Icc τlo τhi))
    (hθ : ∀ τ ∈ Set.Icc τlo τhi, MonotoneOn (q τ) (Set.Icc θlo θhi)) :
    ∃ t : ℝ → ℝ → ℝ, (⟨q, t⟩ : DirectMechanism τlo τhi θlo θhi).Admissible ∧
      (⟨q, t⟩ : DirectMechanism τlo τhi θlo θhi).IsIC E := by sorry

end MechanismDesign.Dynamic

