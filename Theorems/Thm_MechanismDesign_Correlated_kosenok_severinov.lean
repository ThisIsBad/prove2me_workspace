import Mathlib
import Definitions.Def_MechanismDesign_Correlated_FiniteModel

namespace MechanismDesign.Correlated

open FiniteTypes

/-- Börgers, Proposition 6.6 (p.127), after Kosenok and Severinov (2008). Types are finite and
every type vector has positive prior probability. If the prior `μ` satisfies the Crémer–McLean
and the identifiability conditions, then for every ex ante budget balanced direct mechanism
`(q, t)` there is a Bayesian incentive-compatible, ex post budget balanced direct mechanism
`(q, t')` with the same decision rule and the same interim expected payments. -/
theorem kosenok_severinov {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] {A : Type*}
    (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (hCM : CremerMcLean μ)
    (hId : Identifiable μ) (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism ι Θ A)
    (hBB : IsExAnteBB μ M) :
    ∃ M' : DirectMechanism ι Θ A, M'.q = M.q ∧
      (∀ i (θi : Θ i), condExp μ i θi (M.t i) = condExp μ i θi (M'.t i)) ∧
      IsBIC μ u M' ∧ IsExPostBB M' := by sorry

end MechanismDesign.Correlated

