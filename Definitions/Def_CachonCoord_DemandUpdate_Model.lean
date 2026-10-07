import Mathlib
import Definitions.Def_SupplyChainTheory_contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

/-- Cachon (2003), 3rd draft (Jan. 2003), §6.6.1, pp. 63–64: the newsvendor with one forecast
update (after Donohue 2000).

* `D ξ` is the law of demand after the demand signal `ξ ≥ 0` is observed; its distribution
  function `F(x|ξ)` is `cdf (D ξ) x`. Demand is nonnegative, has a finite mean, and (the
  chapter's standing assumption, p. 7) `F(·|ξ)` is continuous and strictly increasing on `[0, ∞)`.
* Demand is stochastically increasing in the signal (p. 63): `F(x|ξ_h) < F(x|ξ_l)` for
  `ξ_h > ξ_l` (stated for `x > 0`; at `x ≤ 0` both sides are `0`).
* `ξ ↦ D ξ` is measurable (a Markov kernel), so expectations over the signal make sense.
* The signal has density `g` on `[0, ∞)` (page's `g(·)`), and demand has a finite
  unconditional mean `∫ E[D|ξ] g(ξ) dξ < ∞`.
* `p` is the retail price, `c1 < c2` the supplier's unit production costs in periods 1 and 2
  (page's `c_1, c_2`); `0 < c2 < p` makes the critical ratio `(p − c_2)/p` of (25) lie in `(0, 1)`.
  Salvage value and lost-sales costs are normalized to zero (p. 64). -/
structure Model where
  /-- Conditional demand law given the signal `ξ`. -/
  D : ℝ → Measure ℝ
  isProb : ∀ ξ, 0 ≤ ξ → IsProbabilityMeasure (D ξ)
  nonneg : ∀ ξ, 0 ≤ ξ → D ξ (Set.Iio 0) = 0
  integrable : ∀ ξ, 0 ≤ ξ → Integrable (fun x : ℝ => x) (D ξ)
  continuous_cdf : ∀ ξ, 0 ≤ ξ → Continuous (cdf (D ξ))
  strictMono_cdf : ∀ ξ, 0 ≤ ξ → StrictMonoOn (cdf (D ξ)) (Set.Ici 0)
  /-- Demand is stochastically increasing in the demand signal (p. 63). -/
  stoch_incr : ∀ ξl ξh x : ℝ, 0 ≤ ξl → ξl < ξh → 0 < x → cdf (D ξh) x < cdf (D ξl) x
  measurable_D : Measurable D
  /-- Density `g` of the demand signal on `[0, ∞)`. -/
  g : ℝ → ℝ
  g_measurable : Measurable g
  g_nonneg : ∀ ξ, 0 ≤ g ξ
  g_integrable : IntegrableOn g (Set.Ici 0)
  g_total : ∫ ξ in Set.Ici (0 : ℝ), g ξ = 1
  /-- Finite unconditional mean demand. -/
  mean_integrable : IntegrableOn (fun ξ => (∫ x, x ∂(D ξ)) * g ξ) (Set.Ici 0)
  /-- Retail price `p`. -/
  p : ℝ
  /-- Period-1 unit production cost `c_1`. -/
  c1 : ℝ
  /-- Period-2 unit production cost `c_2`. -/
  c2 : ℝ
  c1_lt_c2 : c1 < c2
  c2_pos : 0 < c2
  c2_lt_p : c2 < p

namespace Model

variable (M : Model)

/-- The conditional demand distribution function `F(x|ξ)`. -/
noncomputable def F (ξ x : ℝ) : ℝ := cdf (M.D ξ) x

/-- Conditional expected sales `S(q|ξ) = E[min(q, D) | ξ]` (§6.2, p. 10, with the law `F(·|ξ)`). -/
noncomputable def S (ξ q : ℝ) : ℝ := SupplyChainTheory.expSales (M.D ξ) q

/-- The signal's distribution function `G(t) = ∫_0^t g(ξ) dξ`. -/
noncomputable def G (t : ℝ) : ℝ := ∫ ξ in Set.Icc 0 t, M.g ξ

/-- Expectation over the signal: `E[h(ξ)] = ∫_0^∞ h(ξ) g(ξ) dξ`. -/
noncomputable def E (h : ℝ → ℝ) : ℝ := ∫ ξ in Set.Ici (0 : ℝ), h ξ * M.g ξ

/-- The critical ratio `(p − c_2)/p` of (25)–(26). -/
noncomputable def ratio : ℝ := (M.p - M.c2) / M.p

/-- Eq. (24), p. 64: the supply chain's expected revenue minus the period-2 production cost,
`Ω_2(q_2|q_1, ξ) = pS(q_2|ξ) − c_2 q_2 + c_2 q_1`. -/
noncomputable def Omega2 (q1 ξ q2 : ℝ) : ℝ := M.p * M.S ξ q2 - M.c2 * q2 + M.c2 * q1

/-- `q2sel q1 ξ` is a supply-chain optimal total order `q_2(q_1, ξ)` (p. 64): for every
`q_1 ≥ 0` and signal `ξ ≥ 0` it maximizes `Ω_2(·|q_1, ξ)` over `q_2 ≥ q_1` (period-1 stock
cannot be returned). -/
def IsChainPeriod2Optimal (q2sel : ℝ → ℝ → ℝ) : Prop :=
  ∀ q1 ξ : ℝ, 0 ≤ q1 → 0 ≤ ξ →
    q1 ≤ q2sel q1 ξ ∧ IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) (q2sel q1 ξ)

/-- p. 66: the supply chain's expected profit `Ω_1(q_1) = −c_1 q_1 + E[Ω_2(q_2(q_1, ξ)|q_1, ξ)]`,
for a selection `q2sel` of the period-2 optimum `q_2(q_1, ξ)`. -/
noncomputable def Omega1 (q2sel : ℝ → ℝ → ℝ) (q1 : ℝ) : ℝ :=
  -M.c1 * q1 + M.E (fun ξ => M.Omega2 q1 ξ (q2sel q1 ξ))

end Model

end CachonCoord.DemandUpdate
