import Mathlib
import Definitions.Def_SatiaLave_Bayes_Model

open MeasureTheory

namespace SatiaLave.Bayes

/-- Proof of Proposition 10, p. 736: the Bayesian optimal return dominates the expected
(under the prior) total discounted return `∫ [q + β P^A q + β² [P^A]² q + ⋯]_i dg(P)` of every
pure stationary policy `A`. -/
theorem bayes_return_ge_stationary_policy {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D)
    (f : S → Measure (Mat S D) → ℝ) (hf : SolvesEq10 M f) (hb : IsBoundedOnPriors f)
    (g : Measure (Mat S D)) (hg : IsPrior g) (A : (i : S) → D i) (i : S) :
    Integrable (fun P => policyValue M A P i) g ∧
      ∫ P, policyValue M A P i ∂g ≤ f i g := by sorry

end SatiaLave.Bayes

