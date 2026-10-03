import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Bellman

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- A decision rule at time `n` (Bäuerle–Rieder, Definition 2.1.5a, p. 16, PDF 31): a measurable
`f : E → A` with `f(x) ∈ D_n(x)` for all `x`. -/
def IsDecisionRule (M : MarkovDecisionModel E A N) (n : ℕ) (f : E → A) : Prop :=
  Measurable f ∧ ∀ x, (x, f x) ∈ M.D n

/-- An `N`-stage policy (Bäuerle–Rieder, Definition 2.1.5b, p. 16, PDF 31): a sequence of
decision rules `π = (f_0, …, f_{N-1})`. Formalized as a single `f : ℕ → E → A`, measurable at
every `n` (a harmless strengthening for `n ≥ N`, where the book's `f_n` is simply absent — see
`MODERATION_NOTES.md`), whose restriction to `n < N` is a decision rule of `M`. -/
def Policy (M : MarkovDecisionModel E A N) : Type _ :=
  {f : ℕ → E → A // (∀ n, Measurable (f n)) ∧ ∀ n < N, ∀ x, (x, f n x) ∈ M.D n}

lemma Policy.isDecisionRule {M : MarkovDecisionModel E A N} (π : Policy M) {n : ℕ} (hn : n < N) :
    IsDecisionRule M n (π.1 n) :=
  ⟨π.2.1 n, π.2.2 n hn⟩

end MDPFinance.Bellman
