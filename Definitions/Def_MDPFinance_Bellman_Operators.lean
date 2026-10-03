import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Bellman

/-- The integral `∫ v dμ ∈ [-∞,∞)` of an extended-real-valued function `v` that never equals
`⊤`, against a measure `μ`, following the standard convention for extended-real integration:
split `v` into its (finite, since `v ≠ ⊤`) nonnegative part and its (possibly infinite)
nonpositive part, integrate each with `∫⁻`, and combine with `EReal`'s total addition (which
uses the convention `⊤ + (-⊤) = ⊥`, i.e. an a priori ill-defined `∞ - ∞` collapses to `-∞`
rather than being left undefined — matching Def. 2.3.1's own caveat "whenever the integral
exists"). -/
noncomputable def erealIntegral {E : Type*} [MeasurableSpace E] (μ : Measure E) (v : E → EReal) :
    EReal :=
  (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal))

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- The operator `L_n` (Bäuerle–Rieder, Definition 2.3.1a, p. 20, PDF 34):
`(L_n v)(x,a) := r_n(x,a) + ∫ v(x') Q_n(dx'|x,a)`. -/
noncomputable def L (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (xa : E × A) :
    EReal :=
  (M.r n xa : EReal) + erealIntegral (M.Q n xa) v

/-- The operator `T_n^f` (Bäuerle–Rieder, Definition 2.3.1b, p. 20, PDF 34):
`(T_n^f v)(x) := (L_n v)(x, f(x))`. -/
noncomputable def Tf (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (f : E → A) (x : E) :
    EReal :=
  L M n v (x, f x)

/-- The maximal reward operator `T_n` (Bäuerle–Rieder, Definition 2.3.1c, p. 20, PDF 34):
`(T_n v)(x) := sup_{a ∈ D_n(x)} (L_n v)(x,a)`. -/
noncomputable def T (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (x : E) : EReal :=
  ⨆ a ∈ M.Dx n x, L M n v (x, a)

/-- `f` is a maximizer of `v` at time `n` (Bäuerle–Rieder, Definition 2.3.6, p. 21, PDF 36):
a decision rule at time `n` with `T_n^f v = T_n v`, i.e. `f(x)` attains the supremum defining
`T_n v(x)` for every `x`. -/
def IsMaximizer (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (f : E → A) : Prop :=
  IsDecisionRule M n f ∧ Tf M n v f = T M n v

end MDPFinance.Bellman
