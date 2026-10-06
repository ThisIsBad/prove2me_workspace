import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Semicontinuous

/-- A (non-stationary) Markov Decision Model with planning horizon `N` (Bäuerle–Rieder,
Definition 2.1.1, p. 14, PDF 29), restated in this chunk's own sub-namespace since drafts in
this series cannot import one another. See `MDPFinance.Bellman.MarkovDecisionModel`
(chunk `02a`) for the identical definition with the same provenance. -/
structure MarkovDecisionModel (E A : Type*) [MeasurableSpace E] [MeasurableSpace A] (N : ℕ) where
  /-- `D n ⊆ E × A`, the admissible state-action pairs at time `n` (meaningful for `n < N`). -/
  D : ℕ → Set (E × A)
  hD_meas : ∀ n < N, MeasurableSet (D n)
  /-- `D n` contains the graph of a measurable decision rule. -/
  hD_sel : ∀ n < N, ∃ f : E → A, Measurable f ∧ ∀ x, (x, f x) ∈ D n
  /-- The transition kernel `Q_n(·|x,a)`. -/
  Q : ℕ → Kernel (E × A) E
  hQ_prob : ∀ n < N, ∀ xa, IsProbabilityMeasure (Q n xa)
  /-- The one-stage reward `r_n(x,a)`. -/
  r : ℕ → E × A → ℝ
  hr_meas : ∀ n < N, Measurable (r n)
  /-- The terminal reward `g_N(x)`. -/
  g : E → ℝ
  hg_meas : Measurable g

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- `D_n(x) = {a ∈ A | (x,a) ∈ D_n}`, the admissible actions in state `x` at time `n`. -/
def MarkovDecisionModel.Dx (M : MarkovDecisionModel E A N) (n : ℕ) (x : E) : Set A :=
  {a | (x, a) ∈ M.D n}

end MDPFinance.Semicontinuous
