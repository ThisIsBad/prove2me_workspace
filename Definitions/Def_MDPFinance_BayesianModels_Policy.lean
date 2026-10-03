import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.BayesianModels

variable {EX Θ A Z : Type*} [MeasurableSpace EX] [MeasurableSpace Θ] [MeasurableSpace A]
  [MeasurableSpace Z]

/-- A decision rule at stage `n` is a function of the full observable history so far,
`h̃_n = (x_0,a_0,z_1,x_1,\dots,a_{n-1},z_n,x_n)` (Bäuerle–Rieder, p. 149-151, PDF 162-164),
represented as a triple `(xs,as,zs)` of (junk-padded) sequences `ℕ → E_X`, `ℕ → A`, `ℕ → Z`
(`zs 0` is unused junk since `z`-indices start at `1`); a *policy* is a sequence of such rules. -/
def Policy (EX A Z : Type*) := (n : ℕ) → (ℕ → EX) → (ℕ → A) → (ℕ → Z) → A

/-- `f` is a decision rule at stage `n`: measurable, depends only on `h̃_n` (not on later
coordinates), and feasible, `f(h̃_n) ∈ D(x_n)` (Bäuerle–Rieder, Definition 5.1.3a specialized to
the Bayesian Model, p. 150, PDF 163). -/
def BayesModel.IsDecisionRule (M : BayesModel EX Θ A Z) (n : ℕ)
    (f : (ℕ → EX) → (ℕ → A) → (ℕ → Z) → A) : Prop :=
  Measurable (fun p : (ℕ → EX) × (ℕ → A) × (ℕ → Z) => f p.1 p.2.1 p.2.2) ∧
    (∀ xs xs' as as' zs zs', (∀ i ≤ n, xs i = xs' i) → (∀ i < n, as i = as' i) →
      (∀ i, 1 ≤ i → i ≤ n → zs i = zs' i) → f xs as zs = f xs' as' zs') ∧
    ∀ xs as zs, f xs as zs ∈ M.Dx (xs n)

/-- `π` is an `N`-stage policy: `π n` is a decision rule at stage `n` for every `n < N`
(Bäuerle–Rieder, Definition 5.1.3b, p. 150, PDF 163). -/
def BayesModel.IsPolicy (M : BayesModel EX Θ A Z) (N : ℕ) (π : Policy EX A Z) : Prop :=
  ∀ n < N, M.IsDecisionRule n (π n)

end MDPFinance.BayesianModels
