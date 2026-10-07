import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

namespace Model

variable (M : Model)

/-- Options contract `(w_o, w_e)` (§6.10.2, p. 99): `M` buys `q_i` options at `w_o` each in stage 1
and pays `w_e` per option exercised in stage 2. With `k = q_i` the type-`θ` manufacturer's expected
profit is `Π_θ(q_i) = (r − w_e) S_θ(q_i) − w_o q_i`. -/
noncomputable def mfrProfit (θ : DemandType) (we wo qi : ℝ) : ℝ :=
  (M.r - we) * M.S θ qi - wo * qi

/-- The supplier's expected profit under the options contract `(w_o, w_e)` when he builds
`k = q_i` (forced compliance, §6.10.2–6.10.3, pp. 99–100 and 103): he receives `w_o q_i` and
`w_e S_θ(q_i)`, pays `c_k q_i` for capacity and `c_p S_θ(q_i)` for production. -/
noncomputable def supProfit (θ : DemandType) (we wo qi : ℝ) : ℝ :=
  (we - M.cp) * M.S θ qi + wo * qi - M.ck * qi

/-- The exercise price of the coordinating options contract with share `λ` (`lam`), chosen so that
`r − w_e = λ (r − c_p)` (p. 99). -/
def optWe (lam : ℝ) : ℝ := M.r - lam * (M.r - M.cp)

/-- The option price of the coordinating options contract with share `λ` (`lam`), `w_o = λ c_k`
(p. 99). -/
def optWo (lam : ℝ) : ℝ := lam * M.ck

/-- Voluntary compliance (§6.10.2, p. 100): the profit `π(k, q_i, τ) = (w_e − c_p) S_τ(k) + w_o q_i − c_k k`
of a supplier who believes demand is type `τ` and builds capacity `k` (the page's formula, stated
for `k < q_i`) after selling `q_i` options. -/
noncomputable def supVoluntaryProfit (τ : DemandType) (we wo k qi : ℝ) : ℝ :=
  (we - M.cp) * M.S τ k + wo * qi - M.ck * k

/-- Wholesale price contract under voluntary compliance (§6.10.2, p. 101): the supplier's profit
`π_θ(k) = (w − c_p) S_θ(k) − c_k k` from building capacity `k`. -/
noncomputable def supWholesaleProfit (θ : DemandType) (w k : ℝ) : ℝ :=
  (w - M.cp) * M.S θ k - M.ck * k

/-- The wholesale price that makes capacity `k` optimal for the supplier (p. 101):
`w_θ(k) = c_k / F̄_θ(k) + c_p`, with `F̄_θ(k) = 1 − F(k|θ)`. (If `F̄_θ(k) = 0` Lean's `x / 0 = 0`
gives `c_p`; the theorems using it assume `F̄_θ(k) > 0`.) -/
noncomputable def wInduce (θ : DemandType) (k : ℝ) : ℝ :=
  M.ck / (1 - cdf (M.μ θ) k) + M.cp

/-- The manufacturer's profit when she induces capacity `k` with the wholesale price `w_θ(k)`
(p. 101): `Π_θ(k) = (r − w_θ(k)) S_θ(k)`. -/
noncomputable def mfrWholesaleProfit (θ : DemandType) (k : ℝ) : ℝ :=
  (M.r - M.wInduce θ k) * M.S θ k

/-- The low type's share in the forced-compliance separating contracts (§6.10.3, p. 104),
`λ_l = 1 − π̂ / Ω_l°`, where `kl` is the low type's optimal capacity `k_l°` and `piHat` is the
supplier's minimum acceptable profit `π̂`. -/
noncomputable def shareLow (kl piHat : ℝ) : ℝ := 1 - piHat / M.Omega DemandType.l kl

/-- `λ_h = 1 − π̂ / Ω_h°` (p. 104), `kh` the high type's optimal capacity `k_h°`. -/
noncomputable def shareHigh (kh piHat : ℝ) : ℝ := 1 - piHat / M.Omega DemandType.h kh

/-- `λ̂_h = (Ω_l° − π̂) / Ω_l(k_h°)` (p. 104). -/
noncomputable def shareHighHat (kh kl piHat : ℝ) : ℝ :=
  (M.Omega DemandType.l kl - piHat) / M.Omega DemandType.l kh

end Model

end CachonCoord.CapacityForecast
