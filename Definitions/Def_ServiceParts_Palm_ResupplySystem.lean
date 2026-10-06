import Mathlib

open MeasureTheory ProbabilityTheory

namespace ServiceParts.Palm

/-- The backorder (s–1, s) resupply system of Muckstadt (2005), Section 3.1, pp. 37–40.
Customer orders arrive as a Poisson process with rate `rate` = λ, realised through i.i.d.
exponential interarrival times `gap k` (the `k`-th order, counted from `0`, is placed at time
`gap 0 + ⋯ + gap k`); each order immediately triggers a resupply order whose resupply time is
`resupply k`. Resupply times are i.i.d., nonnegative, have a density and a finite mean, and the
whole family of interarrival and resupply times is mutually independent (so resupply times are
independent of the arrival process). The system is empty at time `0`. The stock level `s` is not
part of the model: in the backorder case the number of units in resupply does not depend on it. -/
structure ResupplySystem (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  /-- the customer order arrival rate λ -/
  rate : ℝ
  /-- interarrival times of the Poisson order stream -/
  gap : ℕ → Ω → ℝ
  /-- resupply time of the `k`-th order -/
  resupply : ℕ → Ω → ℝ
  /-- the common density `g` of the resupply times -/
  density : ℝ → ENNReal
  rate_pos : 0 < rate
  gap_measurable : ∀ k, Measurable (gap k)
  resupply_measurable : ∀ k, Measurable (resupply k)
  density_measurable : Measurable density
  /-- interarrival times are exponential with rate λ (Poisson order process) -/
  gap_law : ∀ k, P.map (gap k) = expMeasure rate
  /-- every resupply time has density `g` -/
  resupply_law : ∀ k, P.map (resupply k) = volume.withDensity density
  /-- resupply times are nonnegative -/
  resupply_nonneg : ∀ k ω, 0 ≤ resupply k ω
  /-- the mean resupply time τ̄ is finite -/
  resupply_integrable : Integrable (resupply 0) P
  /-- all interarrival and resupply times are mutually independent -/
  indep : iIndepFun (Sum.elim gap resupply) P

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The epoch `T_k = gap 0 + ⋯ + gap k` at which the `k`-th customer order (counted from `0`)
is placed. -/
noncomputable def ResupplySystem.arrival (S : ResupplySystem Ω P) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), S.gap i ω

/-- `N(t)`: the number of customer orders placed in `[0, t]` (`0` on the null event where
infinitely many orders fall in `[0, t]`). -/
noncomputable def ResupplySystem.orderCount (S : ResupplySystem Ω P) (t : ℝ) (ω : Ω) : ℕ :=
  {k : ℕ | S.arrival k ω ≤ t}.ncard

/-- `X(t)`: the number of units in resupply at time `t`, i.e. the number of orders placed by
time `t` whose resupply is not complete at time `t` (`T_k ≤ t < T_k + L_k`). -/
noncomputable def ResupplySystem.unitsInResupply (S : ResupplySystem Ω P) (t : ℝ) (ω : Ω) : ℕ :=
  {k : ℕ | S.arrival k ω ≤ t ∧ t < S.arrival k ω + S.resupply k ω}.ncard

/-- The resupply-time distribution function `G(u) = P[L ≤ u]`. -/
noncomputable def ResupplySystem.resupplyCdf (S : ResupplySystem Ω P) (u : ℝ) : ℝ :=
  (P {ω | S.resupply 0 ω ≤ u}).toReal

/-- The mean resupply time `τ̄ = E[L]`. -/
noncomputable def ResupplySystem.meanResupply (S : ResupplySystem Ω P) : ℝ :=
  ∫ ω, S.resupply 0 ω ∂P

end ServiceParts.Palm
