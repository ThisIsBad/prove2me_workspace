import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Stationary

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- A decision rule for a stationary Markov Decision Model (Bäuerle–Rieder, p. 39, PDF 54): a
measurable `f : E → A` with `f(x) ∈ D(x)` for all `x` (the set of all such is written `F`). -/
def IsDecisionRule (M : StationaryMarkovDecisionModel E A) (f : E → A) : Prop :=
  Measurable f ∧ ∀ x, (x, f x) ∈ M.D

/-- A **policy sequence of length `n`**, `π : ℕ → E → A` with `π k` a decision rule for every
`k < n` (Bäuerle–Rieder's `π = (f_0,…,f_{n-1}) ∈ F^n`, p. 39, PDF 54). `π` is left as a total
function on `ℕ`; only `π k` for `k < n` is constrained. -/
def IsPolicySeq (M : StationaryMarkovDecisionModel E A) (n : ℕ) (π : ℕ → E → A) : Prop :=
  ∀ k < n, IsDecisionRule M (π k)

end MDPFinance.Stationary
