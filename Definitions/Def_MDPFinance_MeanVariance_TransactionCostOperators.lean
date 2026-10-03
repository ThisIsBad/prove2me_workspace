import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The maximal reward operator `T_n v(x) := sup_{a ∈ Arange(x)} 𝔼[v(h(x,a)(1+i_{n+1}),
a\,\tilde R_{n+1})]` (Bäuerle–Rieder, p. 107-108, PDF 122). -/
noncomputable def TransactionCostMarket.T (M : TransactionCostMarket Ω) (n : ℕ)
    (v : ℝ × ℝ → ℝ) (x0 x1 : ℝ) : ℝ :=
  ⨆ a ∈ M.Arange x0 x1, ∫ ω, v (M.h x0 x1 a * (1 + M.i (n + 1)), a * M.Rtilde (n + 1) ω) ∂M.measIP

/-- `v ∈ IM` (Bäuerle–Rieder, p. 107, PDF 121): `v ∈ IB_b^+` for the upper bounding function
`b(x) = 1 + x0 + x1` (measurable, `v^+ ≤ c·b` on `E`), increasing in each component, concave
and homogeneous of degree `γ` on the state space `E = ℝ_{\ge0}²`. -/
def IsInIM (γ : ℝ) (v : ℝ × ℝ → ℝ) : Prop :=
  Measurable v ∧ (∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ Estate, max (v x) 0 ≤ c * (1 + x.1 + x.2)) ∧
  (∀ x ∈ Estate, ∀ y ∈ Estate, x.1 ≤ y.1 → x.2 ≤ y.2 → v x ≤ v y) ∧
    ConcaveOn ℝ Estate v ∧ IsHomogeneousDeg γ v

/-- `f ∈ Δ` (Bäuerle–Rieder, Eq. (4.26), p. 109, PDF 123): `f` is a buy/hold/sell decision rule,
i.e. there are `0 ≤ q^- ≤ q^+ ≤ ∞` and measurable `f^+, f^- : E → ℝ_{\ge0}` with
`f(x0,x1) = f^+(x0,x1)` if `x1/x0 > q^+`, `= x1` if `q^- ≤ x1/x0 ≤ q^+`, `= f^-(x0,x1)` if
`x1/x0 < q^-`, and `f^+(x0,x1) < x1`, `f^-(x0,x1) > x1` (on the respective regions of `E`; the
ratio `x1/x0` is `ratio x0 x1 ∈ [0,∞]`). -/
def IsBuyHoldSellRule (f : ℝ × ℝ → ℝ) : Prop :=
  ∃ qm qp : EReal, 0 ≤ qm ∧ qm ≤ qp ∧ ∃ fp fm : ℝ × ℝ → ℝ, Measurable fp ∧ Measurable fm ∧
    (∀ x ∈ Estate, qp < ratio x.1 x.2 → f x = fp x ∧ fp x < x.2) ∧
    (∀ x ∈ Estate, qm ≤ ratio x.1 x.2 → ratio x.1 x.2 ≤ qp → f x = x.2) ∧
    (∀ x ∈ Estate, ratio x.1 x.2 < qm → f x = fm x ∧ x.2 < fm x)

end MDPFinance.MeanVariance
