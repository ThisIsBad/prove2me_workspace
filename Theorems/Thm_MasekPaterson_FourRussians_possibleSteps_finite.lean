import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Shared_steps
open MasekPaterson.Shared

namespace MasekPaterson.FourRussians

/-- Lemma 4: over a finite alphabet, if the set `Ω` of edit costs is discrete then the set
of possible steps in edit matrices is finite. -/
theorem possibleSteps_finite {α : Type*} [Fintype α] (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hΩ : IsDiscrete γ) :
    (possibleSteps γ).Finite := by sorry

end MasekPaterson.FourRussians

