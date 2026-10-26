import Mathlib.Probability.Kernel.SetIntegral

open MeasureTheory ProbabilityTheory

namespace SmithHitAndRun.SymMixing

/-- Assumption (a) for the transition kernel, together with the pointwise symmetry of the
transition density asserted for symmetric mixing algorithms on Smith's p. 1299. The strictly
positive density in Assumption (b) is stated separately where needed. -/
def IsSymmetricMixingKernel {α : Type*} [MeasurableSpace α]
    (V : Measure α) (P : Kernel α α) (f : α → α → ENNReal) : Prop :=
  Measurable (Function.uncurry f) ∧
  (∀ x A, MeasurableSet A → P x A = ∫⁻ y in A, f y x ∂V) ∧
  (∀ x y, f y x = f x y)

end SmithHitAndRun.SymMixing
