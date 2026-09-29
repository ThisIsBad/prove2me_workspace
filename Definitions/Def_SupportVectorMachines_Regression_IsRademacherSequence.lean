import Mathlib

open MeasureTheory ProbabilityTheory

namespace SupportVectorMachines.Regression

/-- A finite family `ε : Fin n → Θ → ℝ` **is a Rademacher sequence with respect to `ν`**
(Steinwart & Christmann, *Support Vector Machines*, Springer 2008, p. 535, before Theorem A.8.1,
restated locally per Hard Rule 9): the `εᵢ` are independent, and each `εᵢ` takes the values `1`
and `-1` each with `ν`-probability `1/2`. -/
def IsRademacherSequence {Θ : Type*} [MeasurableSpace Θ] {n : ℕ} (ε : Fin n → Θ → ℝ)
    (ν : Measure Θ) : Prop :=
  (∀ i, Measurable (ε i)) ∧ iIndepFun ε ν ∧
    ∀ i, ν {θ : Θ | ε i θ = 1} = 1 / 2 ∧ ν {θ : Θ | ε i θ = -1} = 1 / 2

end SupportVectorMachines.Regression
