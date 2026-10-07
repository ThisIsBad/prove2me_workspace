import Mathlib
import Definitions.Def_MechanismDesign_Robust_TypeSpaces

open scoped ENNReal

namespace MechanismDesign.Robust

/-- Proposition 10.1 (Börgers p.174). In a finite type space whose beliefs are derived from a
common prior `μ` with full support, conditional on any profile of belief types
`β ∈ ∏_i β̂_i(T_i)`, the payoff types are independent:
`μ((θ_1, …, θ_N) | β) = μ(θ_1 | β) ⋯ μ(θ_N | β)` for every payoff type profile `θ`. -/
theorem payoff_types_conditionally_independent {ι : Type} [Fintype ι] [DecidableEq ι]
    {Θ : ι → Type*} {T : ι → Type*} [∀ i, Fintype (T i)] (ts : TypeSpace Θ T)
    (μ : PMF (∀ i, T i)) (hμ : ts.IsCommonPrior μ) (hfull : ∀ τ, μ τ ≠ 0)
    (β : ∀ i, PMF (Others T i)) (hβ : ∀ i, β i ∈ Set.range (ts.β i)) (θ : ∀ i, Θ i) :
    condProb μ {τ | ts.payoff τ = θ} {τ | ts.beliefs τ = β} =
      ∏ i, condProb μ {τ | ts.payoff τ i = θ i} {τ | ts.beliefs τ = β} := by sorry

end MechanismDesign.Robust

