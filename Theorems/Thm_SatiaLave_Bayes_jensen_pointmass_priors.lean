import Mathlib
import Definitions.Def_SatiaLave_Bayes_Model

open MeasureTheory

namespace SatiaLave.Bayes

/-- Proof of Proposition 9, p. 736 (first line of the display): writing a prior `g` as the
mixture `∫ δ_P dg(P)` of point masses, Jensen's inequality for the convex function `f(i, ·)`
gives `f(i, g) ≤ ∫ f(i, δ_P) dg(P)`. -/
theorem jensen_pointmass_priors {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D)
    (f : S → Measure (Mat S D) → ℝ) (hf : SolvesEq10 M f) (hb : IsBoundedOnPriors f)
    (g : Measure (Mat S D)) (hg : IsPrior g) (i : S) :
    Integrable (fun P => f i (Measure.dirac P)) g ∧
      f i g ≤ ∫ P, f i (Measure.dirac P) ∂g := by sorry

end SatiaLave.Bayes

