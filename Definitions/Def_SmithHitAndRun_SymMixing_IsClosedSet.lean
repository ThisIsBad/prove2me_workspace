import Mathlib.Probability.Kernel.Basic

open MeasureTheory ProbabilityTheory

namespace SmithHitAndRun.SymMixing

/-- A measurable nonempty set that the chain cannot leave in one step from any of its points. -/
def IsClosedSet {α : Type*} [MeasurableSpace α] (P : Kernel α α) (A : Set α) : Prop :=
  A.Nonempty ∧ MeasurableSet A ∧ ∀ x ∈ A, P x A = 1

end SmithHitAndRun.SymMixing
