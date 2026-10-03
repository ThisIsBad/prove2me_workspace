import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

/-- The integral `∫ v dμ ∈ [-∞,∞)` of an extended-real-valued function `v` that never equals
`⊤` (restated from `MDPFinance.Bellman.erealIntegral`, chunk `02a`; `⊤ + (-⊤) = ⊥`), so that an
expected utility equal to `-∞` is recorded as `-∞`, never as a default real value. -/
noncomputable def erealIntegral {E : Type*} [MeasurableSpace E] (μ : Measure E) (v : E → EReal) :
    EReal :=
  (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal))

/-- Strict concavity of an `EReal`-valued function on `s ⊆ ℝ` (restated from chunk `04a`). -/
def StrictConcaveOnEReal (s : Set ℝ) (f : ℝ → EReal) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
    (a : EReal) * f x + (b : EReal) * f y < f (a * x + b * y)

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The one-period consumption-investment problem's admissible set (Bäuerle–Rieder, p. 94, PDF
108): `D(x) := {(c,a) ∈ ℝ_{\ge0} × ℝ^d | 0 ≤ c ≤ x, (1+i)(x-c+a\cdot R) ∈ domUp ℙ-a.s.}`, the
consumption `c` lying in the (common) domain of the utility functions. -/
def OnePeriodCID (measIP : Measure Ω) (domUp : Set ℝ) (i : ℝ) (R : Ω → Fin d → ℝ) (x : ℝ) :
    Set (ℝ × (Fin d → ℝ)) :=
  {ca | 0 ≤ ca.1 ∧ ca.1 ≤ x ∧ ca.1 ∈ domUp ∧
    ∀ᵐ ω ∂measIP, (1 + i) * (x - ca.1 + ∑ k, ca.2 k * R ω k) ∈ domUp}

/-- `u(x,c,a) := U_c(c) + 𝔼[U_p((1+i)(x-c+a\cdot R))] ∈ [-∞, ∞)` (Bäuerle–Rieder, p. 94, PDF 108). -/
noncomputable def OnePeriodCIU (measIP : Measure Ω) (Uc Up : ℝ → ℝ) (i : ℝ)
    (R : Ω → Fin d → ℝ) (x : ℝ) (ca : ℝ × (Fin d → ℝ)) : EReal :=
  (Uc ca.1 : EReal) +
    erealIntegral measIP (fun ω => (Up ((1 + i) * (x - ca.1 + ∑ k, ca.2 k * R ω k)) : EReal))

/-- `v(x) := sup_{(c,a) ∈ D(x)} u(x,c,a)` (Bäuerle–Rieder, p. 94, PDF 108). -/
noncomputable def OnePeriodCIV (measIP : Measure Ω) (domUp : Set ℝ) (Uc Up : ℝ → ℝ) (i : ℝ)
    (R : Ω → Fin d → ℝ) (x : ℝ) : EReal :=
  ⨆ ca ∈ OnePeriodCID measIP domUp i R x, OnePeriodCIU measIP Uc Up i R x ca

/-- No arbitrage for the one-period market (Bäuerle–Rieder, Theorem 3.1.5(b)/4.1.1, restated for
this chunk): no `a ∈ ℝ^d` with `a·R ≥ 0` `ℙ`-a.s. and `ℙ(a·R > 0) > 0`. -/
def NoArbitrageOnePeriodCI (measIP : Measure Ω) (R : Ω → Fin d → ℝ) : Prop :=
  ¬ ∃ a : Fin d → ℝ, (∀ᵐ ω ∂measIP, 0 ≤ ∑ k, a k * R ω k) ∧
    measIP {ω | 0 < ∑ k, a k * R ω k} > 0

end MDPFinance.ConsumptionInvestment
