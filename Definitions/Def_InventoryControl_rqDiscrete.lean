import Mathlib

namespace InventoryControl

/-- A lead-time demand distribution on the nonnegative integers with finite mean:
`p j = P(D(L) = j)`. Axsäter, *Inventory Control*, Sect. 6.1.1. -/
structure DiscreteDemand where
  p : ℕ → ℝ
  nonneg : ∀ j, 0 ≤ p j
  hasSum : HasSum p 1
  summable_mean : Summable (fun j : ℕ => (j : ℝ) * p j)

/-- The mean lead-time demand `μ' = μ L`. -/
noncomputable def DiscreteDemand.mean (D : DiscreteDemand) : ℝ := ∑' j : ℕ, (j : ℝ) * D.p j

/-- `P(D(L) ≤ k)` for an integer `k`; zero for `k < 0`. -/
noncomputable def DiscreteDemand.cdf (D : DiscreteDemand) (k : ℤ) : ℝ :=
  ∑ j ∈ Finset.Icc (0 : ℤ) k, D.p j.toNat

/-- `g(k)`: the average holding and shortage cost rate when the inventory position is kept at
`k`, Axsäter, *Inventory Control*, Eq. (6.3) and Eq. (6.20):
`g(k) = -b₁ (k - μ') + (h + b₁) ∑_{j=1}^{k} j P(D(L) = k - j)`. -/
noncomputable def sPolicyCost (D : DiscreteDemand) (h b1 : ℝ) (k : ℤ) : ℝ :=
  -b1 * ((k : ℝ) - D.mean) + (h + b1) * ∑ j ∈ Finset.Icc (1 : ℤ) k, (j : ℝ) * D.p (k - j).toNat

/-- `C(R, Q) = Aμ/Q + (1/Q) ∑_{k=R+1}^{R+Q} g(k)`, the total average cost rate of an `(R, Q)`
policy whose inventory position is uniform on `{R+1, …, R+Q}`. Axsäter, *Inventory Control*,
Eq. (6.4). -/
noncomputable def rqDiscreteCost (D : DiscreteDemand) (h b1 A μ : ℝ) (R : ℤ) (Q : ℕ) : ℝ :=
  A * μ / Q + (1 / (Q : ℝ)) * ∑ j ∈ Finset.range Q, sPolicyCost D h b1 (R + 1 + j)

/-- The ready rate `S₃ = P(IL > 0) = (1/Q) ∑_{k=R+1}^{R+Q} P(D(L) ≤ k - 1)` of an `(R, Q)`
policy, Axsäter, *Inventory Control*, Eq. (5.50) with Eq. (5.36). -/
noncomputable def rqDiscreteReadyRate (D : DiscreteDemand) (R : ℤ) (Q : ℕ) : ℝ :=
  (1 / (Q : ℝ)) * ∑ j ∈ Finset.range Q, D.cdf (R + j)

end InventoryControl
