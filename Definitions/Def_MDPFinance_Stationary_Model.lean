import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Stationary

/-- A stationary Markov Decision Model (Bäuerle–Rieder, p. 39-40, PDF 54-55, intro to §2.5): the
data `(E, A, D, Q, r, g)` does not depend on the stage `n`; the reward at time `n` is `β^n r` and
the terminal reward at time `N` is `β^N g`, for a discount factor `β ∈ (0,1]`. -/
structure StationaryMarkovDecisionModel (E A : Type*) [MeasurableSpace E] [MeasurableSpace A] where
  /-- `D ⊆ E × A`, the admissible state-action pairs. -/
  D : Set (E × A)
  hD_meas : MeasurableSet D
  /-- `D` contains the graph of a measurable decision rule. -/
  hD_sel : ∃ f : E → A, Measurable f ∧ ∀ x, (x, f x) ∈ D
  /-- The (time-homogeneous) transition kernel `Q(·|x,a)`. -/
  Q : Kernel (E × A) E
  hQ_prob : ∀ xa, IsProbabilityMeasure (Q xa)
  /-- The one-stage reward `r(x,a)`. -/
  r : E × A → ℝ
  hr_meas : Measurable r
  /-- The one-stage terminal/holding reward `g(x)`. -/
  g : E → ℝ
  hg_meas : Measurable g
  /-- The discount factor `β ∈ (0,1]`. -/
  β : ℝ
  hβ_pos : 0 < β
  hβ_le_one : β ≤ 1

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- `D(x) = {a ∈ A | (x,a) ∈ D}`, the admissible actions in state `x`. -/
def StationaryMarkovDecisionModel.Dx (M : StationaryMarkovDecisionModel E A) (x : E) : Set A :=
  {a | (x, a) ∈ M.D}

end MDPFinance.Stationary
