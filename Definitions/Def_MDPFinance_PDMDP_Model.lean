import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Core

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.PDMDP

/-- The control-function space `A := {α : ℝ₊ → U measurable}` (Bäuerle–Rieder, Eq. (8.1)),
rendered as the subtype of measurable functions `ℝ → U`. -/
def ControlFn (U : Type*) [MeasurableSpace U] := {α : ℝ → U // Measurable α}

instance instMeasurableSpaceControlFn (U : Type*) [MeasurableSpace U] :
    MeasurableSpace (ControlFn U) :=
  Subtype.instMeasurableSpace

/-- The relaxed control-function space `R := {α : ℝ₊ → ℙ(U) measurable}` (Bäuerle–Rieder,
Eq. (8.6), p. 249, PDF 260). -/
def RelaxedControlFn (U : Type*) [MeasurableSpace U] :=
  {α : ℝ → ProbabilityMeasure U // Measurable α}

instance instMeasurableSpaceRelaxedControlFn (U : Type*) [MeasurableSpace U] :
    MeasurableSpace (RelaxedControlFn U) :=
  Subtype.instMeasurableSpace

/-- The strong Carathéodory functions `Car(ℝ₊ × U)` (Bäuerle–Rieder, Remark 8.2.3, p. 249, PDF
260): continuous in `u`, measurable in `t`, with `∫_0^∞ max_u |w(t,u)| dt < ∞`. -/
def IsCaratheodory {U : Type*} [MeasurableSpace U] [TopologicalSpace U] (w : ℝ × U → ℝ) : Prop :=
  (∀ t, Continuous fun u => w (t, u)) ∧ (∀ u, Measurable fun t => w (t, u)) ∧
    (∫⁻ t in Set.Ioi (0 : ℝ), ⨆ u, ENNReal.ofReal |w (t, u)|) < ⊤

/-- The **Young topology** on relaxed controls (Bäuerle–Rieder, Remark 8.2.3, p. 249, PDF 260):
the coarsest topology making `α ↦ ∫_0^∞ ∫_U w(t,u) α_t(du) dt` continuous for every
`w ∈ Car(ℝ₊ × U)`. With it `R` is a compact metrizable Borel space and `A` is dense in `R`. -/
noncomputable def youngTopology (U : Type*) [MeasurableSpace U] [TopologicalSpace U] :
    TopologicalSpace (ℝ → ProbabilityMeasure U) :=
  ⨅ w ∈ {w : ℝ × U → ℝ | IsCaratheodory w},
    TopologicalSpace.induced
      (fun α : ℝ → ProbabilityMeasure U =>
        ∫ t in Set.Ioi (0 : ℝ), ∫ u, w (t, u) ∂(α t).toMeasure)
      inferInstance

/-- Definition 8.1.1 (Bäuerle–Rieder, p. 243-244, PDF 254-255). A Piecewise Deterministic Markov
Decision Model consists of `(E,U,μ,λ,Q,r,β)`: `E` the state space (a Borel subset of `ℝ^d`; here
a real normed space, of which `ℝ^d` is the case in the book), `U` a Borel control space, `A` the
control functions, `μ(x,u) ∈ E` the measurable deterministic drift, and for every `α ∈ A` the
unique solution `φ_t^α(x)` of `ẋ_t = μ(x_t,α_t)`, `x_0 = x` — bundled as data `φ` satisfying the
initial value problem in integral (Carathéodory) form, continuous in `t` and measurable in
`(α,x)`; the relaxed flow `φRel` solving `ẋ_t = ∫ μ(x_t,u) α_t(du)` for relaxed controls (Eq.
(8.7)), consistent with `φ` on point masses; `Q` a stochastic kernel from `E × U` to `E`
(jump-goal distribution); `λ > 0` the Poisson jump rate; `r : E × U → ℝ` the measurable reward
rate; `β ≥ 0` the discount rate. The book's own σ-algebra on `A` (the coarsest making
`α ↦ ∫_0^∞ e^{-t} w(t,α_t) dt` measurable) is rendered by the product σ-algebra on `ℝ → U`. -/
structure PDMDPModel (E U : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [MeasurableSpace U] [TopologicalSpace U] where
  μ : E × U → E
  hμ_meas : Measurable μ
  φ : ℝ → (ℝ → U) → E → E
  hφ0 : ∀ α x, φ 0 α x = x
  /-- `φ^α_·(x)` solves `ẋ_t = μ(x_t,α_t)`, `x_0 = x` (integral form). -/
  hφ_ode : ∀ (α : ℝ → U), Measurable α → ∀ x, ∀ t, 0 ≤ t →
    φ t α x = x + ∫ s in (0 : ℝ)..t, μ (φ s α x, α s)
  hφ_cont : ∀ α x, Continuous fun t => φ t α x
  hφ_meas : ∀ t, Measurable fun p : (ℝ → U) × E => φ t p.1 p.2
  /-- The **relaxed** flow, solving `ẋ_t = ∫ μ(x_t,u) α_t(du)`, `x_0 = x` (Eq. (8.7)). -/
  φRel : ℝ → (ℝ → ProbabilityMeasure U) → E → E
  hφRel0 : ∀ α x, φRel 0 α x = x
  hφRel_ode : ∀ (α : ℝ → ProbabilityMeasure U), Measurable α → ∀ x, ∀ t, 0 ≤ t →
    φRel t α x = x + ∫ s in (0 : ℝ)..t, ∫ u, μ (φRel s α x, u) ∂(α s).toMeasure
  hφRel_pt : ∀ t (α : ℝ → U) (_hα : Measurable α) x,
    φRel t (fun s => (⟨Measure.dirac (α s), inferInstance⟩ : ProbabilityMeasure U)) x = φ t α x
  Q : Kernel (E × U) E
  isMarkovQ : IsMarkovKernel Q
  lam : ℝ
  hlam : 0 < lam
  r : E × U → ℝ
  hr_meas : Measurable r
  β : ℝ
  hβ : 0 ≤ β

end MDPFinance.PDMDP
