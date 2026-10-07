import Mathlib
import Definitions.Def_MechanismDesign_Correlated_FiniteModel

namespace MechanismDesign.Correlated

open FiniteTypes

/-- Börgers, Proposition 6.4 (p.121), after Crémer and McLean (1988). Types are finite and every
type vector has positive prior probability. If the prior `μ` satisfies the Crémer–McLean
condition, then for every direct mechanism `(q, t)` there is a Bayesian incentive-compatible direct
mechanism `(q, t')` with the same decision rule and the same interim expected payments
`∑_{θ₋ᵢ} tᵢ(θᵢ, θ₋ᵢ) μ(θ₋ᵢ | θᵢ) = ∑_{θ₋ᵢ} t'ᵢ(θᵢ, θ₋ᵢ) μ(θ₋ᵢ | θᵢ)` for all `i` and `θᵢ`. -/
theorem cremer_mclean {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] {A : Type*}
    (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (hCM : CremerMcLean μ)
    (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism ι Θ A) :
    ∃ M' : DirectMechanism ι Θ A, M'.q = M.q ∧
      (∀ i (θi : Θ i), condExp μ i θi (M.t i) = condExp μ i θi (M'.t i)) ∧
      IsBIC μ u M' := by sorry

end MechanismDesign.Correlated

