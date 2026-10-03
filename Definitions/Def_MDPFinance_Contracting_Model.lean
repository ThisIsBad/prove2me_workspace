import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Contracting

/-- Definition 7.1.1 (Bäuerle–Rieder, p. 194, PDF 205): a stationary Markov Decision Model with
infinite horizon, data `(E,A,D,Q,r,β)` as in Definition 2.1.1 (`D` measurable containing the graph
of a measurable map, `Q` a stochastic kernel, `r` measurable), no terminal reward (`g ≡ 0`). The
operators below drop the time index `n` and bake the discount `β` directly into `L`, unlike the
finite-horizon series' own time-indexed operators. -/
structure MarkovDecisionModel (E A : Type*) [MeasurableSpace E] [MeasurableSpace A] where
  D : Set (E × A)
  hD_meas : MeasurableSet D
  /-- `D` contains the graph of a measurable map (Definition 2.1.1), so `D(x) ≠ ∅`. -/
  hD_graph : ∃ f : E → A, Measurable f ∧ ∀ x, (x, f x) ∈ D
  Q : Kernel (E × A) E
  isMarkovQ : IsMarkovKernel Q
  r : E × A → ℝ
  hr_meas : Measurable r
  β : ℝ
  hβ0 : 0 < β
  hβ1 : β ≤ 1

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- `D(x) := {a ∈ A | (x,a) ∈ D}`. -/
def MarkovDecisionModel.Dx (M : MarkovDecisionModel E A) (x : E) : Set A :=
  {a | (x, a) ∈ M.D}

/-- `IM(E)`: measurable `E → [-∞,∞)`-valued functions (Bäuerle–Rieder p. 19, PDF 34), restated. -/
def IM (E : Type*) [MeasurableSpace E] : Set (E → EReal) :=
  {v | Measurable v ∧ ∀ x, v x ≠ ⊤}

/-- The extended-real integral, restated from `MDPFinance.Bellman.erealIntegral` (chunk `02a`). -/
noncomputable def erealIntegral (μ : Measure E) (v : E → EReal) : EReal :=
  (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal))

/-- `f` is a decision rule for `D`: measurable, `f(x) ∈ D(x)`. -/
def IsDecisionRuleOf (M : MarkovDecisionModel E A) (f : E → A) : Prop :=
  Measurable f ∧ ∀ x, (x, f x) ∈ M.D

/-- `Lv(x,a) := r(x,a) + β ∫ v(x') Q(dx'|x,a)` (Bäuerle–Rieder, p. 197, PDF 209, stationary,
discount baked in). -/
noncomputable def L (M : MarkovDecisionModel E A) (v : E → EReal) (xa : E × A) : EReal :=
  (M.r xa : EReal) + (M.β : EReal) * erealIntegral (M.Q xa) v

/-- `T_f v(x) := Lv(x,f(x))`. -/
noncomputable def Tf (M : MarkovDecisionModel E A) (f : E → A) (v : E → EReal) (x : E) : EReal :=
  L M v (x, f x)

/-- `Tv(x) := sup_{a ∈ D(x)} Lv(x,a)`. -/
noncomputable def T (M : MarkovDecisionModel E A) (v : E → EReal) (x : E) : EReal :=
  ⨆ a ∈ M.Dx x, L M v (x, a)

/-- `T°v(x) := sup_{a ∈ D(x)} β ∫ v(x') Q(dx'|x,a)` (Bäuerle–Rieder, Definition 7.1.2, p. 195,
PDF 206): the pure time-shift operator, no reward term, distinct from `T`. -/
noncomputable def Tcirc (M : MarkovDecisionModel E A) (v : E → EReal) (x : E) : EReal :=
  ⨆ a ∈ M.Dx x, (M.β : EReal) * erealIntegral (M.Q (x, a)) v

/-- `f` is a maximizer of `v` (Def. 2.3.6, restated): a decision rule realizing `T`'s supremum at
every state. -/
def IsMaximizerOf (M : MarkovDecisionModel E A) (v : E → EReal) (f : E → A) : Prop :=
  IsDecisionRuleOf M f ∧ (fun x => L M v (x, f x)) = T M v

end MDPFinance.Contracting
