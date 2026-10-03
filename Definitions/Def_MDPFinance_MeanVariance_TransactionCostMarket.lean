import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- The terminal-wealth Markov Decision Model with proportional transaction costs
(Bäuerle–Rieder, p. 106-107, PDF 120-121): state `(x0,x1) ∈ E := ℝ_{\ge0}²` (bond, stock
holdings), transition `T_n((x0,x1),a,z) := (h(x0,x1,a)(1+i_{n+1}), a z)` where `a ∈ [0, x1 +
x0/(1+c)]` is the stock holding *after* transaction and `h` (p. 108, PDF 122, unnumbered
display) accounts for the proportional cost `c ∈ [0,1)` paid from the bond; `r_n ≡ 0`,
`g_N(x0,x1) := U(x0+x1)` for a utility function `U` homogeneous of degree `γ`; the section's
standing Assumption (FM) (homogeneity, `𝔼 R̃_n < ∞`), independent price changes and positive bond
factors are fields. Reduced to the
scalar action `a` (the post-transaction stock holding) per the book's own reduction (p. 108, PDF
122: "it is enough to determine the amount invested in the stock after transaction"). -/
structure TransactionCostMarket (Ω : Type*) [MeasurableSpace Ω] where
  measIP : Measure Ω
  isProb : IsProbabilityMeasure measIP
  N : ℕ
  i : ℕ → ℝ
  hi_pos : ∀ n, 1 ≤ n → n ≤ N → 0 < 1 + i n
  c : ℝ
  hc0 : 0 ≤ c
  hc1 : c < 1
  Rtilde : ℕ → Ω → ℝ
  hRtilde_meas : ∀ n, 1 ≤ n → n ≤ N → Measurable (Rtilde n)
  hRtilde_pos : ∀ n, 1 ≤ n → n ≤ N → ∀ᵐ ω ∂measIP, 0 < Rtilde n ω
  /-- The relative price changes `R̃_1, …, R̃_N` are independent ("the independent disturbances"). -/
  hRtilde_indep : iIndepFun (fun n : Fin N => Rtilde (n.val + 1)) measIP
  /-- Assumption (FM)(ii): `𝔼‖R̃_n‖ < ∞`. -/
  hRtilde_int : ∀ n, 1 ≤ n → n ≤ N → Integrable (Rtilde n) measIP
  γ : ℝ
  /-- The utility function `U` (Definition 3.4.1, `dom U = [0,∞)`), homogeneous of degree `γ`
  (Assumption (FM)(i)). -/
  U : ℝ → ℝ
  hU_mono : StrictMonoOn U (Set.Ici 0)
  hU_concave : StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) U
  hU_cont : ContinuousOn U (Set.Ici (0 : ℝ))
  hU_hom : ∀ x ≥ (0 : ℝ), ∀ lam > (0 : ℝ), U (lam * x) = lam ^ γ * U x

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `h(x,a)` (Bäuerle–Rieder, p. 108, PDF 122, unnumbered display), the bond holding after
buying/selling stock to reach post-transaction stock holding `a`, transaction costs paid from
the bond. -/
noncomputable def TransactionCostMarket.h (M : TransactionCostMarket Ω) (x0 x1 a : ℝ) : ℝ :=
  if a ≤ x1 then x0 + (1 - M.c) * (x1 - a) else x0 + (1 + M.c) * (x1 - a)

/-- The admissible post-transaction stock holdings, `0 ≤ a ≤ x1 + x0/(1+c)` (Bäuerle–Rieder,
p. 108, PDF 122). -/
def TransactionCostMarket.Arange (M : TransactionCostMarket Ω) (x0 x1 : ℝ) : Set ℝ :=
  Set.Icc 0 (x1 + x0 / (1 + M.c))

/-- The state space `E := ℝ_{\ge0}²` of bond and stock holdings. -/
def Estate : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ 0 ≤ x.2}

/-- A function `f : E → ℝ` is homogeneous of degree `γ` (Bäuerle–Rieder, p. 107, PDF 121):
`f(λx) = λ^γ f(x)` for `λ > 0` and `x ∈ E`. -/
def IsHomogeneousDeg (γ : ℝ) (f : ℝ × ℝ → ℝ) : Prop :=
  ∀ lam > (0 : ℝ), ∀ x ∈ Estate, f (lam * x.1, lam * x.2) = lam ^ γ * f x

/-- The stock-to-bond ratio `x1/x0 ∈ [0, ∞]` of a state `x ∈ E`, with `x1/0 = ∞` for `x1 > 0`
(and `0/0 := 0`), as the book's regions `x1/x0 > q^+`, `x1/x0 < q^-` read it. -/
noncomputable def ratio (x0 x1 : ℝ) : EReal :=
  if x0 = 0 then (if x1 = 0 then (0 : EReal) else ⊤) else ((x1 / x0 : ℝ) : EReal)

end MDPFinance.MeanVariance
