import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CachonCoord_PriceNewsvendor_Demand

namespace CachonCoord.PriceNewsvendor

/-- The one-supplier, one-retailer price-dependent newsvendor of §6.3. -/
structure Model where
  demand : DemandFamily
  cs : ℝ
  cr : ℝ
  gs : ℝ
  gr : ℝ
  v : ℝ
  cs_nonneg : 0 ≤ cs
  cr_nonneg : 0 ≤ cr
  gs_nonneg : 0 ≤ gs
  gr_nonneg : 0 ≤ gr
  price_above_cost : ∀ p ∈ demand.prices, cs + cr < p
  salvage_below_cost : v < cs + cr

namespace Model

variable (M : Model)

/-- Total per-unit production and procurement cost. -/
def c : ℝ := M.cs + M.cr

/-- Total goodwill penalty per unit of unmet demand. -/
def g : ℝ := M.gs + M.gr

/-- Jointly feasible stocking quantities and retail prices. -/
def feasible : Set (ℝ × ℝ) := Set.Ici 0 ×ˢ M.demand.prices

/-- Expected sales `S(q,p) = E_p[min(q,D)]`. -/
noncomputable def S (q p : ℝ) : ℝ :=
  SupplyChainTheory.expSales (M.demand.law p) q

/-- Price-dependent mean demand `μ(p) = E_p[D]`. -/
noncomputable def mu (p : ℝ) : ℝ :=
  SupplyChainTheory.meanDemand (M.demand.law p)

/-- Integrated channel profit on p. 34. -/
noncomputable def Pi (q p : ℝ) : ℝ :=
  (p - M.v + M.g) * M.S q p - (M.c - M.v) * q - M.g * M.mu p

/-- Retailer profit with wholesale price `wb` and buyback payment `b`, p. 35. -/
noncomputable def buybackRetailer (wb b q p : ℝ) : ℝ :=
  (p - M.v + M.gr - b) * M.S q p -
    (wb - b + M.cr - M.v) * q - M.gr * M.mu p

/-- Supplier profit with the same buyback contract, by the p. 17 transfer convention. -/
noncomputable def buybackSupplier (wb b q p : ℝ) : ℝ :=
  (b + M.gs) * M.S q p + (wb - b - M.cs) * q - M.gs * M.mu p

/-- Retailer profit with revenue share `phi` and wholesale price `wr`, p. 36. -/
noncomputable def revenueRetailer (wr phi q p : ℝ) : ℝ :=
  (phi * (p - M.v) + M.gr) * M.S q p -
    (wr + M.cr - phi * M.v) * q - M.gr * M.mu p

/-- The price-dependent buyback rate printed on p. 35. -/
def contingentB (lam p : ℝ) : ℝ :=
  (1 - lam) * (p - M.v + M.g) - M.gs

/-- The price-dependent wholesale price printed on p. 35. -/
def contingentW (lam p : ℝ) : ℝ :=
  lam * M.cs + (1 - lam) * (p + M.g - M.cr) - M.gs

/-- Coordinating revenue-sharing wholesale price when goodwill penalties vanish, p. 37. -/
def revenueW (lam : ℝ) : ℝ :=
  lam * (M.c - M.v) - M.cr + lam * M.v

/-- Retailer profit under the quantity-flexibility contract `(w_q, δ)`, printed on p. 34. -/
noncomputable def qfRetailer (wq δ q p : ℝ) : ℝ :=
  (p - M.v + M.gr) * M.S q p - (wq + M.cr - M.v) * q +
    (wq + M.cr - M.v) * (∫ y in (1 - δ) * q..q, cdfOf (M.demand.law p) y) - M.mu p * M.gr

/-- The quantity-discount schedule `w_d(q)` of p. 38, designed at the price `p0`. -/
noncomputable def qdW (lam p0 q : ℝ) : ℝ :=
  ((1 - lam) * (p0 - M.v + M.g) - M.gs) * (M.S q p0 / q) + lam * (M.c - M.v) - M.cr + M.v

/-- Retailer profit under the quantity discount `w_d(q)`, p. 37. -/
noncomputable def qdRetailer (lam p0 q p : ℝ) : ℝ :=
  (p - M.v + M.gr) * M.S q p - (M.qdW lam p0 q + M.cr - M.v) * q - M.gr * M.mu p

/-- Supplier profit under the quantity discount `w_d(q)`: wholesale revenue less
production cost and the supplier's goodwill cost on expected lost sales. -/
noncomputable def qdSupplier (lam p0 q p : ℝ) : ℝ :=
  M.gs * M.S q p + (M.qdW lam p0 q - M.cs) * q - M.gs * M.mu p

end Model
end CachonCoord.PriceNewsvendor
