import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Bellman

/-- `IM E` (Bäuerle–Rieder p. 19, PDF 34): the measurable functions `E → [-∞, ∞)`, i.e. `EReal`
valued, measurable, and never equal to `⊤`. Value functions and solutions of the Bellman
equation live here rather than in `E → ℝ`, since a supremum over unboundedly bad rewards can be
`-∞`. -/
def IM (E : Type*) [MeasurableSpace E] : Set (E → EReal) :=
  {v | Measurable v ∧ ∀ x, v x ≠ ⊤}

/-- A (non-stationary) Markov Decision Model with planning horizon `N` (Bäuerle–Rieder,
Definition 2.1.1, p. 14, PDF 29). Time is indexed by `ℕ` rather than `Fin N`; only `n < N`
carries meaning; `D`, `Q`, `r` are unconstrained (junk) for `n ≥ N`. `D n` is the measurable set
of admissible state-action pairs at time `n`, required to contain the graph of some measurable
decision rule; `Q n` is the stochastic transition kernel; `r n` the one-stage reward; `g` the
terminal reward at time `N`. -/
structure MarkovDecisionModel (E A : Type*) [MeasurableSpace E] [MeasurableSpace A] (N : ℕ) where
  /-- `D n ⊆ E × A`, the admissible state-action pairs at time `n` (meaningful for `n < N`). -/
  D : ℕ → Set (E × A)
  hD_meas : ∀ n < N, MeasurableSet (D n)
  /-- `D n` contains the graph of a measurable decision rule (Bäuerle–Rieder's standing
  assumption on `D_n`, ensuring `F_n` is nonempty). -/
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

end MDPFinance.Bellman
