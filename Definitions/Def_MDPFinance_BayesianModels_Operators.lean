import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.BayesianModels

/-- `IM E` (Bäuerle–Rieder p. 19, PDF 34): the measurable functions `E → [-∞, ∞)`, i.e. `EReal`
valued, measurable, and never equal to `⊤`. Restated from `MDPFinance.Bellman.IM` (chunk `02a`)
/ `MDPFinance.StructuredModels.IM` (chunk `02c`); this chunk's information-based model (Def.
5.4.6) is stationary, so the Bellman operators below are stated directly on raw data
`(D, Q, r, β)` rather than through a re-bundled `MarkovDecisionModel` structure — building a
value of such a structure inside a `noncomputable def` (as `Definition 5.4.6`'s derivation from a
`BayesModel` would require) would force discharging its measurability/selector *hypotheses* with
real proofs inside a definition, which is out of scope for a draft; stating the operators on raw
data avoids that packaging problem while keeping the same mathematical content (see
`MODERATION_NOTES.md`). -/
def IM (E : Type*) [MeasurableSpace E] : Set (E → EReal) :=
  {v | Measurable v ∧ ∀ x, v x ≠ ⊤}

/-- The integral `∫ v dμ ∈ [-∞,∞)` of an extended-real-valued function `v ≠ ⊤`, against a
measure `μ`. Restated from `MDPFinance.Bellman.erealIntegral` (chunk `02a`). -/
noncomputable def erealIntegral {E : Type*} [MeasurableSpace E] (μ : Measure E) (v : E → EReal) :
    EReal :=
  (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal))

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- `f` is a decision rule for the feasible set `D` (Bäuerle–Rieder, Definition 2.1.5a, p. 16,
PDF 31, specialized to a stationary `D`): a measurable `f : E → A` with `f(x) ∈ D(x)` for all
`x`. -/
def IsDecisionRuleOf (D : Set (E × A)) (f : E → A) : Prop :=
  Measurable f ∧ ∀ x, (x, f x) ∈ D

/-- The operator `Lv(x,a) := r(x,a) + β ∫ v(x') Q(dx'|x,a)` (Bäuerle–Rieder, Definition 2.3.1a,
p. 20, PDF 34, stationary + discounted, matching the info-based model's own Bellman equation,
Theorem 5.4.8a). The one-stage reward is `[-∞,∞]`-valued, since the information-based model's
`r̂(x,i,a) = ∫ r(x,θ,a) μ̂(dθ|i)` is defined "whenever the integral exists" (p. 162). -/
noncomputable def Lop (Q : E × A → Measure E) (r : E × A → EReal) (β : ℝ) (v : E → EReal)
    (xa : E × A) : EReal :=
  r xa + (β : EReal) * erealIntegral (Q xa) v

/-- The maximal-reward operator `Tv(x) := sup_{a ∈ D(x)} Lv(x,a)` (Bäuerle–Rieder, Definition
2.3.1c, p. 20, PDF 34, stationary). -/
noncomputable def Top (D : Set (E × A)) (Q : E × A → Measure E) (r : E × A → EReal) (β : ℝ)
    (v : E → EReal) (x : E) : EReal :=
  ⨆ a ∈ {a | (x, a) ∈ D}, Lop Q r β v (x, a)

/-- `f` is a maximizer of `v` (Bäuerle–Rieder, Definition 2.3.6, p. 21, PDF 36, stationary):
a decision rule with `x ↦ Lv(x,f(x))` equal to `Tv`. -/
def IsMaximizerOf (D : Set (E × A)) (Q : E × A → Measure E) (r : E × A → EReal) (β : ℝ)
    (v : E → EReal) (f : E → A) : Prop :=
  IsDecisionRuleOf D f ∧ (fun x => Lop Q r β v (x, f x)) = Top D Q r β v

/-- `k`-fold application of `T`, innermost first: `T (T (⋯ (T v)))`. Used to state Theorem
5.4.8a's Bellman recursion for `k` stages, matching `MDPFinance.Bellman.TChain` (chunk `02a`)
specialized to time-independent data. -/
noncomputable def TChain (D : Set (E × A)) (Q : E × A → Measure E) (r : E × A → EReal) (β : ℝ) :
    (k : ℕ) → (E → EReal) → (E → EReal)
  | 0, v => v
  | (k + 1), v => Top D Q r β (TChain D Q r β k v)

end MDPFinance.BayesianModels
