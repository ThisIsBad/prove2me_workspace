import Mathlib
import Definitions.Def_SatiaLave_Bayes_Model

open MeasureTheory

namespace SatiaLave.Bayes

/-- Propositions 9 and 10: with `α = prob(P ∈ S | g)`,
`α V_i^- + (1 - α) min_{i,j,k} [r^k_{ij}/(1-β)] ≤ f(i, g) ≤ α V_i^+ + (1 - α) max_{i,j,k} [r^k_{ij}/(1-β)]`,
for the bounded solution `f` of (9)/(10) and the solutions `V^+`, `V^-` of the max-max and
max-min equations, all of which exist. -/
theorem bayes_return_bounded_by_maxmax_maxmin {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) :
    (∃ f : S → Measure (Mat S D) → ℝ, SolvesEq10 M f ∧ IsBoundedOnPriors f) ∧
    (∃ V : S → ℝ, SolvesVplus M V) ∧ (∃ V : S → ℝ, SolvesVminus M V) ∧
    ∀ (f : S → Measure (Mat S D) → ℝ), SolvesEq10 M f → IsBoundedOnPriors f →
    ∀ (Vp Vm : S → ℝ), SolvesVplus M Vp → SolvesVminus M Vm →
    ∀ (g : Measure (Mat S D)), IsPrior g → ∀ i : S,
      alpha M g * Vm i + (1 - alpha M g) * rmin M ≤ f i g ∧
        f i g ≤ alpha M g * Vp i + (1 - alpha M g) * rmax M := by sorry

end SatiaLave.Bayes

