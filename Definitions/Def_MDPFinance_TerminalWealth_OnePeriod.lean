import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- The integral `∫ v dμ ∈ [-∞,∞)` of an extended-real-valued function `v` that never equals
`⊤` (restated from `MDPFinance.Bellman.erealIntegral`, chunk `02a`): the Lebesgue integrals of the
positive and negative parts are combined with `EReal`'s total addition (`⊤ + (-⊤) = ⊥`), so an
expected utility that is `-∞` is recorded as `-∞`, never as a default real value. -/
noncomputable def erealIntegral {E : Type*} [MeasurableSpace E] (μ : Measure E) (v : E → EReal) :
    EReal :=
  (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal))

/-- `f` is strictly concave on `s ⊆ ℝ`, for an `EReal`-valued `f` (Mathlib's `StrictConcaveOn`
needs a module structure on the codomain, which `EReal` lacks): `s` is convex and
`a f(x) + b f(y) < f(a x + b y)` for distinct `x, y ∈ s` and `a, b > 0`, `a + b = 1`. -/
def StrictConcaveOnEReal (s : Set ℝ) (f : ℝ → EReal) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
    (a : EReal) * f x + (b : EReal) * f y < f (a * x + b * y)

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The one-period market's admissible actions (Bäuerle–Rieder, p. 77, PDF 91, unnumbered
display): `D(x) := {a ∈ ℝ^d | (1+i)(x + a·R) ∈ domU ℙ-a.s.}`. -/
def OnePeriodD (measIP : Measure Ω) (domU : Set ℝ) (i : ℝ) (R : Ω → Fin d → ℝ) (x : ℝ) :
    Set (Fin d → ℝ) :=
  {a | ∀ᵐ ω ∂measIP, (1 + i) * (x + ∑ k, a k * R ω k) ∈ domU}

/-- `u(x,a) := 𝔼[U((1+i)(x + a·R))] ∈ [-∞, ∞)` (Bäuerle–Rieder, p. 77, PDF 91, unnumbered
display). -/
noncomputable def OnePeriodU (measIP : Measure Ω) (U : ℝ → ℝ) (i : ℝ) (R : Ω → Fin d → ℝ)
    (x : ℝ) (a : Fin d → ℝ) : EReal :=
  erealIntegral measIP (fun ω => (U ((1 + i) * (x + ∑ k, a k * R ω k)) : EReal))

/-- `v(x) := sup_{a ∈ D(x)} u(x,a)` (Bäuerle–Rieder, Eq. (4.2), p. 77, PDF 91). -/
noncomputable def OnePeriodV (measIP : Measure Ω) (domU : Set ℝ) (U : ℝ → ℝ) (i : ℝ)
    (R : Ω → Fin d → ℝ) (x : ℝ) : EReal :=
  ⨆ a ∈ OnePeriodD measIP domU i R x, OnePeriodU measIP U i R x a

/-- The one-period market has no arbitrage opportunities (Bäuerle–Rieder, Theorem 3.1.5(b),
p. 63, PDF 78, specialized to a single period): no `a ∈ ℝ^d` with `a·R ≥ 0` `ℙ`-a.s. and
`ℙ(a·R > 0) > 0`. -/
def NoArbitrageOnePeriod (measIP : Measure Ω) (R : Ω → Fin d → ℝ) : Prop :=
  ¬ ∃ a : Fin d → ℝ, (∀ᵐ ω ∂measIP, 0 ≤ ∑ k, a k * R ω k) ∧
    measIP {ω | 0 < ∑ k, a k * R ω k} > 0

end MDPFinance.TerminalWealth
