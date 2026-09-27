import Mathlib

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

/-- The data of the newsvendor game, Sect. 14.3 (Table 14.3): retail price `r`, per-unit costs
`cs` (supplier) and `cr` (retailer), loss-of-goodwill costs `ps`, `pr`, salvage value `v`, with
`v < cr` and `cs + cr < r`. -/
structure ContractData where
  r : ℝ
  cs : ℝ
  cr : ℝ
  ps : ℝ
  pr : ℝ
  v : ℝ
  cs_nonneg : 0 ≤ cs
  ps_nonneg : 0 ≤ ps
  pr_nonneg : 0 ≤ pr
  v_nonneg : 0 ≤ v
  v_lt_cr : v < cr
  profitable : cs + cr < r

namespace ContractData

/-- `c = cs + cr`. -/
def c (P : ContractData) : ℝ := P.cs + P.cr
/-- `p = ps + pr`. -/
def p (P : ContractData) : ℝ := P.ps + P.pr

end ContractData

/-- (14.1): expected sales `S(Q) = E[min{Q, D}]`. -/
noncomputable def expSales (D : Measure ℝ) (Q : ℝ) : ℝ := ∫ d, min Q d ∂D

/-- (14.3): expected leftover inventory `I(Q) = E[(Q − D)⁺]`. -/
noncomputable def expLeftover (D : Measure ℝ) (Q : ℝ) : ℝ := ∫ d, max (Q - d) 0 ∂D

/-- The mean demand `μ = E[D]`. -/
noncomputable def meanDemand (D : Measure ℝ) : ℝ := ∫ d, d ∂D

/-- (14.5): the retailer's expected profit under a transfer payment `T(Q)`. -/
noncomputable def retailerProfit (P : ContractData) (D : Measure ℝ) (T : ℝ → ℝ) (Q : ℝ) : ℝ :=
  (P.r - P.v + P.pr) * expSales D Q - (P.cr - P.v) * Q - P.pr * meanDemand D - T Q

/-- (14.6): the supplier's expected profit under a transfer payment `T(Q)`. -/
noncomputable def supplierProfit (P : ContractData) (D : Measure ℝ) (T : ℝ → ℝ) (Q : ℝ) : ℝ :=
  P.ps * expSales D Q - P.cs * Q - P.ps * meanDemand D + T Q

/-- (14.7): the supply chain's total expected profit `Π(Q)`. -/
noncomputable def chainProfit (P : ContractData) (D : Measure ℝ) (Q : ℝ) : ℝ :=
  (P.r - P.v + P.p) * expSales D Q - (P.c - P.v) * Q - P.p * meanDemand D

/-- The wholesale price contract, Sect. 14.5: `T_w(Q, w) = wQ`. -/
def wholesaleTransfer (w : ℝ) (Q : ℝ) : ℝ := w * Q

/-- (14.13): the wholesale price at which both players' optimal quantities equal `Q₀`. -/
noncomputable def wholesaleCoordPrice (P : ContractData) : ℝ :=
  P.cs - (P.c - P.v) / (P.r - P.v + P.p) * P.ps

/-- (14.14): `w(Q)`, the wholesale price that makes `Q` optimal for the retailer. -/
noncomputable def wholesaleInducing (P : ContractData) (D : Measure ℝ) (Q : ℝ) : ℝ :=
  (P.r - P.v + P.pr) * (1 - cdf D Q) - (P.cr - P.v)

/-- (14.15): the supplier's profit `πₛ(Q, w(Q))` when she induces the order `Q`. -/
noncomputable def supplierInducedProfit (P : ContractData) (D : Measure ℝ) (Q : ℝ) : ℝ :=
  supplierProfit P D (wholesaleTransfer (wholesaleInducing P D Q)) Q

/-- Increasing generalized failure rate (Sect. 14.5): `Q f(Q) / F̄(Q)` is increasing on `Q > 0`. -/
def IGFR (f : ℝ → ℝ) (D : Measure ℝ) : Prop :=
  MonotoneOn (fun Q => Q * f Q / (1 - cdf D Q)) (Set.Ioi 0)

/-- The buyback contract, Sect. 14.6: `T_b(Q, w, b) = wQ − b I(Q)`. -/
noncomputable def buybackTransfer (D : Measure ℝ) (w b : ℝ) (Q : ℝ) : ℝ := w * Q - b * expLeftover D Q

/-- (14.22): `w(b)`, the coordinating wholesale price for buyback credit `b`. -/
noncomputable def buybackPrice (P : ContractData) (b : ℝ) : ℝ :=
  b + P.cs - (P.c - P.v) * (b + P.ps) / (P.r - P.v + P.p)

/-- (14.25): the retailer's share `λ = (r − v + pr − b) / (r − v + p)` under buyback. -/
noncomputable def buybackShare (P : ContractData) (b : ℝ) : ℝ :=
  (P.r - P.v + P.pr - b) / (P.r - P.v + P.p)

/-- (14.29): the buyback credit `b₁` at which the retailer earns the entire profit. -/
noncomputable def buybackB1 (P : ContractData) (D : Measure ℝ) (Q0 : ℝ) : ℝ :=
  P.r - P.v + P.pr - (P.r - P.v + P.p) * (chainProfit P D Q0 + meanDemand D * P.pr)
    / (chainProfit P D Q0 + meanDemand D * P.p)

/-- (14.30): the buyback credit `b₂` at which the supplier earns the entire profit. -/
noncomputable def buybackB2 (P : ContractData) (D : Measure ℝ) (Q0 : ℝ) : ℝ :=
  P.r - P.v + P.pr - (P.r - P.v + P.p) * (meanDemand D * P.pr)
    / (chainProfit P D Q0 + meanDemand D * P.p)

/-- The revenue sharing contract, Sect. 14.7, (14.33): the retailer keeps a fraction `φ` of sales
and salvage revenue, `T_r(Q, w, φ) = (w + (1 − φ)v) Q + (1 − φ)(r − v) S(Q)`. -/
noncomputable def revenueShareTransfer (P : ContractData) (D : Measure ℝ) (w phi : ℝ) (Q : ℝ) :
    ℝ :=
  (w + (1 - phi) * P.v) * Q + (1 - phi) * (P.r - P.v) * expSales D Q

/-- (14.34): `w(φ)`, the coordinating wholesale price for revenue fraction `φ`. -/
noncomputable def revenueSharePrice (P : ContractData) (phi : ℝ) : ℝ :=
  -P.cr + phi * P.v + (P.c - P.v) * (phi * (P.r - P.v) + P.pr) / (P.r - P.v + P.p)

/-- (14.36): the retailer's share `λ = (φ(r − v) + pr) / (r − v + p)` under revenue sharing. -/
noncomputable def revenueShareLambda (P : ContractData) (phi : ℝ) : ℝ :=
  (phi * (P.r - P.v) + P.pr) / (P.r - P.v + P.p)

/-- The quantity flexibility contract, Sect. 14.8, (14.45):
`T_q(Q, w, δ) = wQ − (w + cr − v) ∫_{(1−δ)Q}^{Q} F(d) dd`. -/
noncomputable def quantityFlexTransfer (P : ContractData) (D : Measure ℝ) (w delta : ℝ) (Q : ℝ) :
    ℝ :=
  w * Q - (w + P.cr - P.v) * ∫ t in (1 - delta) * Q..Q, cdf D t

/-- (14.46): `w(δ)`, the wholesale price making `Q₀` optimal for the retailer. -/
noncomputable def quantityFlexPrice (P : ContractData) (D : Measure ℝ) (Q0 delta : ℝ) : ℝ :=
  (P.r - P.v + P.pr) * (1 - cdf D Q0)
      / ((1 - cdf D Q0) + (1 - delta) * cdf D ((1 - delta) * Q0))
    - P.cr + P.v
end SupplyChainTheory
