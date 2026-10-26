import Mathlib.Probability.Kernel.Invariance

open MeasureTheory

namespace SmithHitAndRun.SymMixing

/-- The uniform law associated with finite nonzero content `V` on the state space. -/
noncomputable def uniformLaw {α : Type*} [MeasurableSpace α] (V : Measure α) : Measure α :=
  (V Set.univ)⁻¹ • V

end SmithHitAndRun.SymMixing
