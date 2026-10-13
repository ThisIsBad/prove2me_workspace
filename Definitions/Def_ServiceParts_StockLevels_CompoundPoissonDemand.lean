import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic

namespace ServiceParts.StockLevels

/-- A single item managed by an `(s-1, s)` policy in the backorder case, with stationary
compound Poisson demand (Muckstadt 2005, Section 3.2, pp. 48-50): customer orders arrive at
rate `λ > 0`, the mean resupply time is `τ̄ > 0`, and each order is for `j` units with
probability `u j`, where `u 0 = 0`, the `u j` are nonnegative and sum to one, and the mean
order size `ū = Σ j u_j` is finite. -/
structure CompoundPoissonDemand where
  /-- customer order rate `λ` -/
  lam : ℝ
  /-- mean resupply time `τ̄` -/
  tbar : ℝ
  /-- order-size distribution: `u j` is the probability that an order is for `j` units -/
  u : ℕ → ℝ
  lam_pos : 0 < lam
  tbar_pos : 0 < tbar
  u_zero : u 0 = 0
  u_nonneg : ∀ j, 0 ≤ u j
  u_hasSum : HasSum u 1
  u_mean : Summable (fun j : ℕ => (j : ℝ) * u j)

namespace CompoundPoissonDemand

variable (d : CompoundPoissonDemand)

/-- Mean order size `ū = Σ_j j u_j`. -/
noncomputable def ubar : ℝ := ∑' j : ℕ, (j : ℝ) * d.u j

/-- Mean lead-time demand `µ = λ τ̄ ū` (Muckstadt 2005, p. 60). -/
noncomputable def mu : ℝ := d.lam * d.tbar * d.ubar

/-- The steady-state probability that `x` units are in resupply (Muckstadt 2005, p. 49):
`p(0|λτ̄) = e^{-λτ̄}` and, for `x ≥ 1`,
`p(x|λτ̄) = Σ_{j=1}^∞ e^{-λτ̄} (λτ̄)^j / j! · u^{(j)}_x`. -/
noncomputable def pmf (x : ℕ) : ℝ :=
  if x = 0 then Real.exp (-(d.lam * d.tbar))
  else ∑' j : ℕ, Real.exp (-(d.lam * d.tbar)) * (d.lam * d.tbar) ^ (j + 1)
      / ((j + 1).factorial : ℝ) * ServiceParts.Palm.convPow d.u (j + 1) x

/-- Ready rate `R(s) = Σ_{x=0}^{s} p(x|λτ̄)` (Muckstadt 2005, p. 49). -/
noncomputable def readyRate (s : ℕ) : ℝ := ∑ x ∈ Finset.range (s + 1), d.pmf x

/-- Expected backorders `B(s) = Σ_{x > s} (x - s) p(x|λτ̄)` (Muckstadt 2005, p. 50). -/
noncomputable def backorders (s : ℕ) : ℝ :=
  ∑' x : ℕ, if s < x then ((x : ℝ) - s) * d.pmf x else 0

/-- Expected on-hand inventory at stock level `s`: on hand is `(s - X)⁺` when `X` units are
in resupply, so `E[On-hand] = Σ_{x ≤ s} (s - x) p(x|λτ̄)` (Muckstadt 2005, p. 60). -/
noncomputable def expectedOnHand (s : ℕ) : ℝ :=
  ∑ x ∈ Finset.range (s + 1), ((s : ℝ) - x) * d.pmf x

end CompoundPoissonDemand

end ServiceParts.StockLevels
