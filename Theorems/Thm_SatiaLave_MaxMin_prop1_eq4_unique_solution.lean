import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Eq4

namespace SatiaLave.MaxMin

/-- Proposition 1, p. 730: the dynamic-programming equations (4), `v_j = eq4Op M v j` for every
state `j`, have exactly one solution, and the max-min return of criterion (2) solves them. -/
theorem prop1_eq4_unique_solution {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) :
    (∃! v : S → ℝ, ∀ j, v j = eq4Op M v j) ∧ ∀ j, maxMinValue M j = eq4Op M (maxMinValue M) j := by sorry

end SatiaLave.MaxMin
