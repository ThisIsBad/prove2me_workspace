import Mathlib
import Definitions.Def_SatiaLave_Bayes_Model

open MeasureTheory

namespace SatiaLave.Bayes

/-- § Bayesian Formulation, p. 733: without learning (a point-mass prior at a transition
matrix `P`, which every Bayes transformation leaves unchanged) the recursion (10) reduces to the
optimality equations of the Markovian decision process with the known matrix `P`. -/
theorem no_learning_reduces_to_mdp {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D)
    (f : S → Measure (Mat S D) → ℝ) (hf : SolvesEq10 M f)
    (P : Mat S D) (hP : IsStoch P) :
    (∀ (l : S) (m : D l) (j : S), bayes (Measure.dirac P) l m j = Measure.dirac P) ∧
    SolvesKnown M P (fun i => f i (Measure.dirac P)) := by sorry

end SatiaLave.Bayes
