import Mathlib
import Definitions.Def_SatiaLave_Bayes_Model

open MeasureTheory

namespace SatiaLave.Bayes

/-- Proposition 6 (Martin): the recursive equations (9)/(10) have a unique bounded solution
(unique on the set of priors, the only arguments at which (10) constrains `f`). -/
theorem prop6_exists_unique_bounded {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) :
    (∃ f : S → Measure (Mat S D) → ℝ, SolvesEq10 M f ∧ IsBoundedOnPriors f) ∧
    ∀ f₁ f₂ : S → Measure (Mat S D) → ℝ,
      SolvesEq10 M f₁ → IsBoundedOnPriors f₁ →
      SolvesEq10 M f₂ → IsBoundedOnPriors f₂ →
      ∀ i g, IsPrior g → f₁ i g = f₂ i g := by sorry

end SatiaLave.Bayes

