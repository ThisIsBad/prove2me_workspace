import Mathlib
import Definitions.Def_DecentralizedDistribution_FirstBest_System
import Definitions.Def_DecentralizedDistribution_FirstBest_DualPrices

open MeasureTheory

namespace DecentralizedDistribution.FirstBest

/-- The non-allocation part of retailer `n`'s profit in Eq. (9):
`r_n S_n + v_n H_n - c_n X_n - ∑_w (c_w - v_w) Y_{w,n}`. -/
def localProfit {N W : ℕ} (sys : System N W) (Z : Profile N W) (D : Demand N) (n : Fin N) : ℝ :=
  sys.r n * sales Z D n + sys.v n * residualInv Z D n - sys.c n * (Z n).X
    - ∑ w, (sys.cw w - sys.vw w) * (Z n).Y w

/-- The centralized profit `P^c_𝒩([Z], D⃗)` of Eqs. (1)–(2a), with all pooled inventory claimed
(`Y_w = ∑_n Y_{w,n}`, p. 361):
`∑_n [r_n S_n + v_n H_n - c_n X_n] - ∑_w (c_w - v_w) Y_w + W*_𝒩([Z], D⃗)`, the last term being
the optimal shipping profit, the value of (2a)–(2e) = (6) for `𝒮 = 𝒩`. -/
noncomputable def centralProfit {N W : ℕ} (sys : System N W) (Z : Profile N W) (D : Demand N) : ℝ :=
  (∑ n, (sys.r n * sales Z D n + sys.v n * residualInv Z D n - sys.c n * (Z n).X))
    - (∑ w, (sys.cw w - sys.vw w) * ∑ n, (Z n).Y w)
    + coalitionValue sys Finset.univ Z D

/-- The expected centralized profit `J^c_𝒩([Z]) = E_D P^c_𝒩([Z], D⃗)` (Eq. (3)). -/
noncomputable def expectedCentralProfit {N W : ℕ} (sys : System N W)
    (μ : Measure (Demand N)) (Z : Profile N W) : ℝ :=
  ∫ D, centralProfit sys Z D ∂μ

/-- A first-best solution (Eq. (4)): a nonnegative profile maximizing `J^c_𝒩` over all
nonnegative profiles. -/
def IsFirstBest {N W : ℕ} (sys : System N W) (μ : Measure (Demand N)) (Z : Profile N W) : Prop :=
  Z.Nonneg ∧ ∀ Z' : Profile N W, Z'.Nonneg → expectedCentralProfit sys μ Z' ≤ expectedCentralProfit sys μ Z

/-- An allocation rule AR-m: a surplus allocation `α^m_n([Z], D⃗)` for every profile, demand
realization and retailer (p. 359). -/
abbrev AllocationRule (N W : ℕ) := Profile N W → Demand N → Fin N → ℝ

/-- Retailer `n`'s total profit under AR-m, Eq. (9):
`P^m_n([Z], D⃗) = r_n S_n + v_n H_n - c_n X_n - ∑_w (c_w - v_w) Y_{w,n} + α^m_n([Z], D⃗)`. -/
def payoff {N W : ℕ} (sys : System N W) (α : AllocationRule N W) (Z : Profile N W)
    (D : Demand N) (n : Fin N) : ℝ :=
  localProfit sys Z D n + α Z D n

/-- Retailer `n`'s expected profit `J^m_n([Z]) = E_D P^m_n([Z], D⃗)`. -/
noncomputable def expectedPayoff {N W : ℕ} (sys : System N W) (μ : Measure (Demand N))
    (α : AllocationRule N W) (Z : Profile N W) (n : Fin N) : ℝ :=
  ∫ D, payoff sys α Z D n ∂μ

/-- A pure-strategy Nash equilibrium of the inventory game under AR-m, Eq. (10): a nonnegative
profile `[Z]` such that no retailer `n` gains by replacing its own position by any nonnegative
position `z`, the other retailers' positions held fixed (`[Z]_{-n} ∪ z`). -/
def IsNashEquilibrium {N W : ℕ} (sys : System N W) (μ : Measure (Demand N))
    (α : AllocationRule N W) (Z : Profile N W) : Prop :=
  Z.Nonneg ∧ ∀ (n : Fin N) (z : Position W), z.Nonneg →
    expectedPayoff sys μ α (Function.update Z n z) n ≤ expectedPayoff sys μ α Z n

/-- The fractional allocation rule AR-f of Eq. (11) with weights `θ`:
`α^f_n([Z], D⃗) = θ_n P^c_𝒩([Z], D⃗) - [r_n S_n + v_n H_n - c_n X_n - ∑_w (c_w - v_w) Y_{w,n}]`
(the sign of `v_n H_n` follows Eq. (9) and the proof of Theorem 5.2, p. 367). -/
noncomputable def fractionalRule {N W : ℕ} (sys : System N W) (θ : Fin N → ℝ) : AllocationRule N W :=
  fun Z D n => θ n * centralProfit sys Z D - localProfit sys Z D n

/-- The side payment of AR-c (proof of Theorem 5.1, p. 367, applied to AR-f at the first-best
`[Z]^{c*}`): `w_n([Z]^{c*}, D⃗) = α^d_n([Z]^{c*}, D⃗) - α^f_n([Z]^{c*}, D⃗)`, where `α^d` is the
dual-price allocation (8) computed from the dual prices `sel D⃗` chosen for each realization. -/
noncomputable def firstBestSidePayment {N W : ℕ} (sys : System N W) (θ : Fin N → ℝ)
    (Zc : Profile N W) (sel : Demand N → DualPrices N W) (n : Fin N) (D : Demand N) : ℝ :=
  dualAllocation Zc D (sel D) n - fractionalRule sys θ Zc D n

/-- The modified fractional allocation rule AR-c of Corollary 5.1:
`α^c_n([Z], D⃗) = α^f_n([Z], D⃗) + w_n([Z]^{c*}, D⃗)`. -/
noncomputable def coreFractionalRule {N W : ℕ} (sys : System N W) (θ : Fin N → ℝ)
    (Zc : Profile N W) (sel : Demand N → DualPrices N W) : AllocationRule N W :=
  fun Z D n => fractionalRule sys θ Z D n + firstBestSidePayment sys θ Zc sel n D

end DecentralizedDistribution.FirstBest
