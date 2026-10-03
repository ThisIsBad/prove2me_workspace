import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- The binomial (Cox-Ross-Rubinstein) Markov Decision Model underlying the mean-risk problem
(Bäuerle–Rieder, p. 125, PDF 139): state space `E := ℝ` (wealth), action space `A := ℝ` (amount
invested in the stock), `D(x) := A`, transition `T(x,a,z) := x+az`, disturbance `z ∈ {d-1,u-1}`
with `ℚ({u-1}) = p`, interest rate `i = 0`; the section's standing Assumption (FM)(i) (no
arbitrage, `d < 1 < u`) and (iii) (`0 < x0 < μ`), independence of the `R_n` and the AVaR level
`γ ∈ (0,1)` are fields ((FM)(ii), `p > q`, is a hypothesis of the theorems, since Theorem 4.7.4
treats `p < q`). -/
structure MeanRiskMarket (Ω : Type*) [MeasurableSpace Ω] where
  measIP : Measure Ω
  isProb : IsProbabilityMeasure measIP
  N : ℕ
  u : ℝ
  d : ℝ
  /-- Assumption (FM)(i): no arbitrage, `d < 1 < u`. -/
  hd_lt_one : d < 1
  hone_lt_u : 1 < u
  p : ℝ
  hp_mem : p ∈ Set.Ioo (0 : ℝ) 1
  R : ℕ → Ω → ℝ
  hR_meas : ∀ n, 1 ≤ n → n ≤ N → Measurable (R n)
  hR_law : ∀ n, 1 ≤ n → n ≤ N → measIP {ω | R n ω = u - 1} = ENNReal.ofReal p ∧
    measIP {ω | R n ω = d - 1} = ENNReal.ofReal (1 - p)
  /-- The relative risks `R_1, …, R_N` are independent (the binomial model of Section 3.1). -/
  hR_indep : iIndepFun (fun n : Fin N => R (n.val + 1)) measIP
  x0 : ℝ
  μ : ℝ
  /-- Assumption (FM)(iii): `0 < x0 < μ`. -/
  hx0 : 0 < x0
  hx0μ : x0 < μ
  /-- The level `γ ∈ (0,1)` of the Average-Value-at-Risk. -/
  γ : ℝ
  hγ : γ ∈ Set.Ioo (0 : ℝ) 1

/-- The risk-neutral up-probability `q := (1-d)/(u-d)` (Bäuerle–Rieder, p. 125, PDF 139). -/
noncomputable def MeanRiskMarket.q {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) : ℝ :=
  (1 - M.d) / (M.u - M.d)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A policy sequence `π : ℕ → ℝ → ℝ` is admissible over `[n,N)` if `π k` is measurable for
every `n ≤ k < N`. -/
def MeanRiskMarket.IsAdmissible (M : MeanRiskMarket Ω) (n : ℕ) (π : ℕ → ℝ → ℝ) : Prop :=
  ∀ k, n ≤ k → k < M.N → Measurable (π k)

/-- The terminal wealth `X_N` reached from state `x` at time `n`, under `π`, on path `ω`. -/
noncomputable def MeanRiskMarket.terminalWealth (M : MeanRiskMarket Ω) (π : ℕ → ℝ → ℝ) :
    (k : ℕ) → (n : ℕ) → (x : ℝ) → (ω : Ω) → ℝ
  | 0, _, x, _ => x
  | (k + 1), n, x, ω => M.terminalWealth π k (n + 1) (x + π n x * M.R (n + 1) ω) ω

/-- `𝔼^π_{x_0}[X_N]`. -/
noncomputable def MeanRiskMarket.meanXN (M : MeanRiskMarket Ω) (π : ℕ → ℝ → ℝ) : ℝ :=
  ∫ ω, M.terminalWealth π M.N 0 M.x0 ω ∂M.measIP

/-- The Average-Value-at-Risk `AVaR_γ(X) := inf_{b∈ℝ} [b + (1-γ)^{-1}𝔼[(X+b)^-]]`
(Bäuerle–Rieder, p. 125-126, PDF 139-140, the Example C.2.2 characterization used throughout
this section). -/
noncomputable def AVaR (measIP : Measure Ω) (γ : ℝ) (X : Ω → ℝ) : ℝ :=
  ⨅ b : ℝ, b + (1 - γ)⁻¹ * ∫ ω, max (-(X ω + b)) 0 ∂measIP

/-- `π*` is optimal for `(MR)` (Bäuerle–Rieder, p. 125, PDF 139): minimizes
`AVaR_γ(X_N)` among admissible `π` with `𝔼^π_{x_0}[X_N] ≥ μ`. -/
def MeanRiskMarket.IsOptimalMR (M : MeanRiskMarket Ω) (πstar : ℕ → ℝ → ℝ) : Prop :=
  M.IsAdmissible 0 πstar ∧ M.μ ≤ M.meanXN πstar ∧
    ∀ π, M.IsAdmissible 0 π → M.μ ≤ M.meanXN π →
      AVaR M.measIP M.γ (M.terminalWealth πstar M.N 0 M.x0) ≤
        AVaR M.measIP M.γ (M.terminalWealth π M.N 0 M.x0)

/-- The value of `(MR)`, `V_{MR}(x_0) := inf` over admissible `π` with `𝔼^π_{x_0}[X_N] ≥ μ` of
`AVaR_γ(X_N)`, as an extended real (`⊤`/`⊥` reserved for infeasible/unbounded, matching the
book's own use of `+∞`/`-∞`). -/
noncomputable def MeanRiskMarket.VMR (M : MeanRiskMarket Ω) : EReal :=
  ⨅ π ∈ {π : ℕ → ℝ → ℝ | M.IsAdmissible 0 π ∧ M.μ ≤ M.meanXN π},
    (AVaR M.measIP M.γ (M.terminalWealth π M.N 0 M.x0) : EReal)

/-- The Lagrange function `L_{x_0}(π,λ) := AVaR_γ(X_N) + λ(μ - 𝔼^π_{x_0}[X_N])`
(Bäuerle–Rieder, p. 126, PDF 140). -/
noncomputable def MeanRiskMarket.Lagrangian (M : MeanRiskMarket Ω) (π : ℕ → ℝ → ℝ) (lam : ℝ) :
    ℝ :=
  AVaR M.measIP M.γ (M.terminalWealth π M.N 0 M.x0) + lam * (M.μ - M.meanXN π)

/-- `π*` is optimal for `P(λ)` (Bäuerle–Rieder, p. 126, PDF 140): minimizes `L_{x_0}(\cdot,λ)`
over admissible `π`. -/
def MeanRiskMarket.IsOptimalPLambda (M : MeanRiskMarket Ω) (lam : ℝ) (πstar : ℕ → ℝ → ℝ) :
    Prop :=
  M.IsAdmissible 0 πstar ∧
    ∀ π, M.IsAdmissible 0 π → M.Lagrangian πstar lam ≤ M.Lagrangian π lam

/-- The value of `P(λ,b)` (Bäuerle–Rieder, p. 126, PDF 140): `inf_π [(1/(1-γ)+λ)𝔼[(X_N+b)^-] -
λ𝔼[(X_N+b)^+]]` over admissible `π`, as an extended real. -/
noncomputable def MeanRiskMarket.VPlambdab (M : MeanRiskMarket Ω) (lam b : ℝ) : EReal :=
  ⨅ π ∈ {π : ℕ → ℝ → ℝ | M.IsAdmissible 0 π},
    (((1 - M.γ)⁻¹ + lam) * ∫ ω, max (-(M.terminalWealth π M.N 0 M.x0 ω + b)) 0 ∂M.measIP -
      lam * ∫ ω, max (M.terminalWealth π M.N 0 M.x0 ω + b) 0 ∂M.measIP : EReal)

/-- `π*` is optimal for `P(λ,b)`. -/
def MeanRiskMarket.IsOptimalPlambdab (M : MeanRiskMarket Ω) (lam b : ℝ)
    (πstar : ℕ → ℝ → ℝ) : Prop :=
  M.IsAdmissible 0 πstar ∧
    (((1 - M.γ)⁻¹ + lam) * ∫ ω, max (-(M.terminalWealth πstar M.N 0 M.x0 ω + b)) 0 ∂M.measIP -
        lam * ∫ ω, max (M.terminalWealth πstar M.N 0 M.x0 ω + b) 0 ∂M.measIP : EReal) =
      M.VPlambdab lam b

end MDPFinance.MeanVariance
