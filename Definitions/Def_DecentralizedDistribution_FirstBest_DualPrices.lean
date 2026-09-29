import Mathlib
import Definitions.Def_DecentralizedDistribution_FirstBest_System

namespace DecentralizedDistribution.FirstBest

/-- A vector of dual prices `(ν, γ, δ)` for the grand-coalition shipping LP (6):
`ν j` for constraint (6b) of retailer `j`, `γ w` for (6c) of warehouse `w`,
`δ n` for (6d) of retailer `n`. -/
abbrev DualPrices (N W : ℕ) := (Fin N → ℝ) × (Fin W → ℝ) × (Fin N → ℝ)

/-- Feasibility in the dual of (6) for the grand coalition `𝒩`: all prices nonnegative and, for
every arc `(i, n)`, `β_{i,n} ν_i + δ_n ≥ β_{i,n} (r_n - v_i - t_{i,n})` (retailer `i`) and
`β_{w,n} γ_w + δ_n ≥ β_{w,n} (r_n - v_w - t_{w,n})` (warehouse `w`). This is the dual constraint
`ν_i + δ_n / β_{i,n} ≥ r_n - v_i - t_{i,n}` of the column `q_{i,n}` multiplied by `β_{i,n}`; it is
vacuous exactly on the arcs with `β_{i,n} = 0`, which carry no shipment. -/
def IsDualFeasible {N W : ℕ} (sys : System N W) (p : DualPrices N W) : Prop :=
  (∀ j, 0 ≤ p.1 j) ∧ (∀ w, 0 ≤ p.2.1 w) ∧ (∀ n, 0 ≤ p.2.2 n) ∧
  (∀ j n, sys.β (Sum.inl j) n * sys.margin (Sum.inl j) n
      ≤ sys.β (Sum.inl j) n * p.1 j + p.2.2 n) ∧
  (∀ w n, sys.β (Sum.inr w) n * sys.margin (Sum.inr w) n
      ≤ sys.β (Sum.inr w) n * p.2.1 w + p.2.2 n)

/-- The dual objective `∑_i ν_i H_i + ∑_w γ_w Y_w + ∑_n δ_n E_n`, with `Y_w = ∑_n Y_{w,n}`. -/
def dualObjective {N W : ℕ} (Z : Profile N W) (D : Demand N) (p : DualPrices N W) : ℝ :=
  (∑ j, p.1 j * residualInv Z D j) + (∑ w, p.2.1 w * ∑ n, (Z n).Y w)
    + ∑ n, p.2.2 n * residualDem Z D n

/-- Dual prices of the shipping problem (6) for `𝒩`: an optimal solution of its dual. -/
def IsOptimalDual {N W : ℕ} (sys : System N W) (Z : Profile N W) (D : Demand N)
    (p : DualPrices N W) : Prop :=
  IsDualFeasible sys p ∧ ∀ p', IsDualFeasible sys p' → dualObjective Z D p ≤ dualObjective Z D p'

/-- The dual-price allocation (8): `α_n = ν_n H_n + ∑_w γ_w Y_{w,n} + δ_n E_n`. -/
def dualAllocation {N W : ℕ} (Z : Profile N W) (D : Demand N) (p : DualPrices N W)
    (n : Fin N) : ℝ :=
  p.1 n * residualInv Z D n + (∑ w, p.2.1 w * (Z n).Y w) + p.2.2 n * residualDem Z D n

end DecentralizedDistribution.FirstBest
