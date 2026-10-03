import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- A decision rule at time `n` (Bäuerle–Rieder, Definition 2.1.5a, p. 16, PDF 31): a measurable
`f : E → A` with `f(x) ∈ D_n(x)` for all `x`. Restated from `MDPFinance.Bellman.IsDecisionRule`
(chunk `02a`); only this one clause of Def. 2.1.5 is needed in this chunk. -/
def IsDecisionRule (M : MarkovDecisionModel E A N) (n : ℕ) (f : E → A) : Prop :=
  Measurable f ∧ ∀ x, (x, f x) ∈ M.D n

end MDPFinance.StructuredModels
