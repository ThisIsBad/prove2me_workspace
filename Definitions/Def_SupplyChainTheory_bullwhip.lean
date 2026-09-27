import Mathlib

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

/-- A stationary Gaussian AR(1) demand process, Snyder-Shen Eq. (13.1): `D t = d + ρ D (t-1) + ε t`
with `ε t` i.i.d. `N(0, σ²)`, each independent of the past demands, and every `D t` distributed
as the stationary law `N(d/(1-ρ), σ²/(1-ρ²))`. -/
structure AR1Demand {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) where
  d : ℝ
  rho : ℝ
  sigma : ℝ
  d_nonneg : 0 ≤ d
  rho_lt : |rho| < 1
  sigma_pos : 0 < sigma
  eps : ℤ → Ω → ℝ
  D : ℤ → Ω → ℝ
  measurable_D : ∀ t, Measurable (D t)
  eps_indep : iIndepFun eps P
  eps_law : ∀ t, P.map (eps t) = gaussianReal 0 (Real.toNNReal (sigma ^ 2))
  eps_indep_past : ∀ t : ℤ, IndepFun (eps t) (fun ω (k : ℕ) => D (t - 1 - k) ω) P
  recursion : ∀ t : ℤ, ∀ ω, D t ω = d + rho * D (t - 1) ω + eps t ω
  stationary : ∀ t, P.map (D t) =
    gaussianReal (d / (1 - rho)) (Real.toNNReal (sigma ^ 2 / (1 - rho ^ 2)))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Eq. (13.7): the moving-average estimate `μ̂ᴸₜ = L (∑_{i=1}^m D_{t-i}) / m`. -/
noncomputable def AR1Demand.muHat (X : AR1Demand P) (L m : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  L * ((∑ i ∈ Finset.Icc 1 m, X.D (t - i) ω) / m)

/-- The one-period forecast error `eₜ = Dₜ − μ̂¹ₜ`. -/
noncomputable def AR1Demand.err (X : AR1Demand P) (m : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  X.D t ω - X.muHat 1 m t ω

/-- Eq. (13.8): `σ̂ᴸₑₜ = C √(∑_{i=1}^m e_{t-i}² / m)`, the book's constant `C_{Lρ}` being the
parameter `C`. -/
noncomputable def AR1Demand.sigmaHat (X : AR1Demand P) (C : ℝ) (m : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  C * Real.sqrt ((∑ i ∈ Finset.Icc 1 m, (X.err m (t - i) ω) ^ 2) / m)

/-- Eq. (13.9): the base-stock level `Sₜ = μ̂ᴸₜ + z_α σ̂ᴸₑₜ`. -/
noncomputable def AR1Demand.baseStock (X : AR1Demand P) (C z : ℝ) (L m : ℕ) (t : ℤ) (ω : Ω) :
    ℝ :=
  X.muHat L m t ω + z * X.sigmaHat C m t ω

/-- The order placed in period `t`: `Qₜ = Sₜ − Sₜ₋₁ + Dₜ₋₁` (p. 544). -/
noncomputable def AR1Demand.order (X : AR1Demand P) (C z : ℝ) (L m : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  X.baseStock C z L m t ω - X.baseStock C z L m (t - 1) ω + X.D (t - 1) ω

/-- Order batching, Sect. 13.2.4: `N` retailers with i.i.d. `N(μ, σ²)` period demands `D i k`
over a reorder interval of `R` periods, and `X` the number of retailers ordering in the period
considered, independent of the demands. -/
structure BatchOrders {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N R : ℕ) (mu sigma : ℝ)
    where
  D : Fin N → Fin R → Ω → ℝ
  X : Ω → ℕ
  measurable_D : ∀ i k, Measurable (D i k)
  measurable_X : Measurable X
  D_indep : iIndepFun (fun p : Fin N × Fin R => D p.1 p.2) P
  D_law : ∀ i k, P.map (D i k) = gaussianReal mu (Real.toNNReal (sigma ^ 2))
  X_indep : IndepFun X (fun ω (p : Fin N × Fin R) => D p.1 p.2 ω) P
  X_le : ∀ ω, X ω ≤ N

/-- The total order received by the supplier: the last `R` demands of each of the `X` ordering
retailers, taken to be retailers `1, …, X` without loss of generality. -/
noncomputable def BatchOrders.supplierOrder {N R : ℕ} {mu sigma : ℝ}
    (B : BatchOrders P N R mu sigma) (ω : Ω) : ℝ :=
  ∑ i : Fin N, if i.val < B.X ω then ∑ k : Fin R, B.D i k ω else 0

/-- Rationing game, Sect. 13.2.3, Eq. (13.14): retailer 1's expected cost when it orders `Q1`,
retailer 2 orders `Q2`, and the supply is `A1` with probability `r` (allocated pro rata) and
unlimited with probability `1 - r`. -/
noncomputable def rationingCost (h p r A1 : ℝ) (Dlaw : Measure ℝ) (Q2 Q1 : ℝ) : ℝ :=
  (1 - r) * (∫ d, (h * max (Q1 - d) 0 + p * max (d - Q1) 0) ∂Dlaw)
    + r * (∫ d, (h * max (A1 * Q1 / (Q1 + Q2) - d) 0
                   + p * max (d - A1 * Q1 / (Q1 + Q2)) 0) ∂Dlaw)

end SupplyChainTheory
