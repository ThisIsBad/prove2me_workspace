import Mathlib
import Definitions.Def_MechanismDesign_Robust_Mechanisms

open scoped ENNReal

namespace MechanismDesign.Robust

/-- Proposition 10.2 (Börgers p.179), the revelation principle on a type space. If `σ` is a
Bayesian equilibrium of the mechanism `(S_1, …, S_N, g)`, then the direct mechanism
`g̃(τ) = g(σ_1(τ_1), …, σ_N(τ_N))` (the lottery induced by `σ` at `τ`) exists, truth telling is a
Bayesian equilibrium of it, and it is outcome equivalent: at every type profile the truthful
outcome lottery of `g̃` equals the equilibrium outcome lottery of `g`. -/
theorem revelation_principle {ι : Type} [Fintype ι] [DecidableEq ι] {Θ T S : ι → Type*}
    {X : Type*} (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ) (M : Mechanism S X)
    (σ : ∀ i, T i → PMF (S i)) (hσ : IsBayesEq ts u M σ) :
    ∃ g' : (∀ i, T i) → PMF X, (∀ τ x, g' τ x = eqOutcome M σ τ x) ∧
      IsBayesEq ts u (directMechanism ts g') (truthful T) ∧
      ∀ τ x, eqOutcome (directMechanism ts g') (truthful T) τ x = eqOutcome M σ τ x := by sorry

end MechanismDesign.Robust

