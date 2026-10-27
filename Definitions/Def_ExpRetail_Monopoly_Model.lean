import Mathlib

namespace ExpRetail.Monopoly

/-- Parameters of the monopoly model of §3.1 (pp. 9–11): `um` = u^m (nominal utility of the main
product), `t` (travel cost), `cm` = c^m (unit cost of the main product), `s` (utility of a
memorable event), `lam` = λ (sensitivity of the synergy), `eta` = η (sensitivity of the
experience cost). -/
structure Params where
  um  : ℝ
  t   : ℝ
  cm  : ℝ
  s   : ℝ
  lam : ℝ
  eta : ℝ

/-- Standing assumptions of §3.1: `t > 0` (p. 9), `η > 0` (p. 11), and `s > 0`, `λ > 0`, which make
`β(u^x) = s(1 − exp(−λ u^x))` positively valued and concave increasing (p. 10). -/
def Params.Standing (P : Params) : Prop := 0 < P.t ∧ 0 < P.eta ∧ 0 < P.s ∧ 0 < P.lam

/-- Brand synergy `β(u^x) = s (1 − exp(−λ u^x))` (p. 10). -/
noncomputable def synergy (P : Params) (ux : ℝ) : ℝ := P.s * (1 - Real.exp (-(P.lam * ux)))

/-- Interaction term `ψ = t + β(u^x)` (p. 10). -/
noncomputable def psi (P : Params) (ux : ℝ) : ℝ := P.t + synergy P ux

/-- Baseline utility of the experience, `v^x = u^x − t` (p. 9). -/
def vx (P : Params) (ux : ℝ) : ℝ := ux - P.t

/-- Baseline utility of the main product at price `p`, `v^m = u^m − t − p` (p. 9). -/
def vm (P : Params) (p : ℝ) : ℝ := P.um - P.t - p

/-- Basket utility `µ_{z^x z^m} = v^x z^x + v^m z^m + ψ z^x z^m` of eq. (3); the first index is the
experience, the second the main product (`0` = not obtained, `1` = obtained). -/
noncomputable def mu (P : Params) (ux p : ℝ) (zx zm : Fin 2) : ℝ :=
  vx P ux * ((zx : ℕ) : ℝ) + vm P p * ((zm : ℕ) : ℝ)
    + psi P ux * ((zx : ℕ) : ℝ) * ((zm : ℕ) : ℝ)

/-- The denominator `Σ_{j,i ∈ {0,1}} exp(µ_{ji})` of eq. (3). -/
noncomputable def partitionSum (P : Params) (ux p : ℝ) : ℝ :=
  ∑ j : Fin 2, ∑ i : Fin 2, Real.exp (mu P ux p j i)

/-- Joint basket probability `q_{z^x z^m}` of eq. (3). -/
noncomputable def basketProb (P : Params) (ux p : ℝ) (zx zm : Fin 2) : ℝ :=
  Real.exp (mu P ux p zx zm) / partitionSum P ux p

/-- Cost of offering an experience of quality `u^x`, `c(u^x) = η (u^x)^2` (p. 11). -/
def expCost (P : Params) (ux : ℝ) : ℝ := P.eta * ux ^ 2

/-- Retailer's profit with a free experience of quality `u^x` at price `p`, eq. (4):
`π(p) = (q01 + q11)(p − c^m) − (q10 + q11) c(u^x)`. -/
noncomputable def profit (P : Params) (ux p : ℝ) : ℝ :=
  (basketProb P ux p 0 1 + basketProb P ux p 1 1) * (p - P.cm)
    - (basketProb P ux p 1 0 + basketProb P ux p 1 1) * expCost P ux

/-- Consumer welfare with the experience: the log-sum `ln Σ_{j,i} exp(µ_{ji})` (convention; the paper
plots `CS*` in Figure 1(d) without defining it). -/
noncomputable def CS (P : Params) (ux p : ℝ) : ℝ := Real.log (partitionSum P ux p)

/-- Purchase probability without an experience, `q1 = exp(v^m) / (exp(v^m) + 1)` (p. 11). -/
noncomputable def q1N (P : Params) (p : ℝ) : ℝ := Real.exp (vm P p) / (Real.exp (vm P p) + 1)

/-- Retailer's profit without an experience, eq. (5): `π(p) = q1 (p − c^m)`. -/
noncomputable def profitN (P : Params) (p : ℝ) : ℝ := q1N P p * (p - P.cm)

/-- Consumer welfare without an experience: the log-sum `ln(1 + exp(v^m))`. -/
noncomputable def CSN (P : Params) (p : ℝ) : ℝ := Real.log (1 + Real.exp (vm P p))

/-- `p` is an optimal price `p*` for eq. (4) at quality `u^x`: a global maximizer over all real prices. -/
def IsOptPrice (P : Params) (ux p : ℝ) : Prop := ∀ p' : ℝ, profit P ux p' ≤ profit P ux p

/-- `p` is an optimal price `p*N` for eq. (5): a global maximizer over all real prices. -/
def IsOptPriceN (P : Params) (p : ℝ) : Prop := ∀ p' : ℝ, profitN P p' ≤ profitN P p

/-- Optimal profit `π*(u^x) = sup_p π(p)` with the experience. -/
noncomputable def optProfit (P : Params) (ux : ℝ) : ℝ := sSup (Set.range (profit P ux))

/-- Optimal profit `π*N = sup_p π(p)` without the experience. -/
noncomputable def optProfitN (P : Params) : ℝ := sSup (Set.range (profitN P))

end ExpRetail.Monopoly
