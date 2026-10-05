import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions

namespace ProcessingNetworks.Stability

open MeasureTheory

/-- Definition 3.6 (SPN stability), Dai & Harrison, p. 47: an SPN satisfying Assumption 3.1 is
stable if the (by Proposition 3.5, mutually equivalent) conditions of that proposition hold. This
mission takes positive recurrence of the ambient continuous-time chain (Definition D.15, through
its jump matrix `M.jump` and exit rates `M.rate`) as the defining clause — one of the three
equivalent statements, per Definition 3.6's own "if"; `equivalent_stability_conditions` (the goal
theorem) is what shows the other two clauses are interchangeable with it. -/
def IsStable {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z) : Prop :=
  PositiveRecurrent M.jump M.rate

end ProcessingNetworks.Stability
