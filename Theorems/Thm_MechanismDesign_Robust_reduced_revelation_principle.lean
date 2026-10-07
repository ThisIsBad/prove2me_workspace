import Mathlib
import Definitions.Def_MechanismDesign_Robust_Mechanisms

open scoped ENNReal

namespace MechanismDesign.Robust

/-- Proposition 10.3 (Börgers p.180), the revelation principle for belief-independent
equilibria. If `σ` is a belief-independent Bayesian equilibrium of `(S_1, …, S_N, g)`, there is a
reduced direct mechanism `g̃ : Θ → Δ(X)` with `g̃(θ̂(τ)) = g(σ_1(τ_1), …, σ_N(τ_N))` for every type
profile `τ` (the book's `g̃(θ) = g(σ(τ))` for any `τ` with `θ̂(τ) = θ`), in which reporting one's
payoff type, `σ̃_i(τ_i) = θ̂_i(τ_i)`, is a Bayesian equilibrium that is outcome equivalent to `σ`. -/
theorem reduced_revelation_principle {ι : Type} [Fintype ι] [DecidableEq ι]
    {Θ T S : ι → Type*} {X : Type*} (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ)
    (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i)) (hσ : IsBayesEq ts u M σ)
    (hbi : IsBeliefIndependent ts σ) :
    ∃ g' : (∀ i, Θ i) → PMF X, (∀ τ x, g' (ts.payoff τ) x = eqOutcome M σ τ x) ∧
      IsBayesEq ts u (reducedMechanism ts g') (truthfulReduced ts) ∧
      ∀ τ x, eqOutcome (reducedMechanism ts g') (truthfulReduced ts) τ x = eqOutcome M σ τ x := by sorry

end MechanismDesign.Robust

