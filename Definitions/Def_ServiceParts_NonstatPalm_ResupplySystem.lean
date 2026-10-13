import Mathlib

open MeasureTheory ProbabilityTheory

namespace ServiceParts.NonstatPalm

/-- The single-location resupply system of Muckstadt (2005), Section 9.1, pp. 215–216, with
nonstationary Poisson demand and time-dependent resupply times.

* Demand rate: `rate` = λ, with λ(s) ≥ 0 and λ integrable on every interval `[0, t]`, so that
  `m(t) = ∫₀ᵗ λ(s) ds` is finite.
* Demand process: the nonstationary Poisson process with mean function `m`, constructed as a
  unit-rate Poisson process time-changed by `m`. The unit-rate process has i.i.d. exponential(1)
  interarrival times `gap k`; its `k`-th point (counted from `0`) is
  `Γ_k = gap 0 + ⋯ + gap k`, and the `k`-th demand occurs at the first time `T_k ≥ 0` with
  `m(T_k) ≥ Γ_k` (see `epoch`). The number of demands in `[0, t]` is `N(t) = #{k : Γ_k ≤ m(t)}`.
* Resupply times: demand `k` carries a random mark `mark k` in a measurable space `E` with law
  `markLaw`; the resupply time of a unit demanded at time `s` with mark `e` is `resupply s e`.
  Hence a unit demanded at time `s` is resupplied within `w` time units with probability
  `G_s(w) = markLaw {e | resupply s e ≤ w}`; resupply times are nonnegative and have finite
  expectation for every demand time `s ≥ 0`.
* Independence: the pairs `(gap k, mark k)` are independent across `k`, and within each pair
  the gap and the mark are independent (the pair's law is the product law). So resupply times
  are independent from unit to unit and independent of the arrival process. -/
structure ResupplySystem (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
    (E : Type*) [MeasurableSpace E] where
  /-- the demand rate λ(t) -/
  rate : ℝ → ℝ
  rate_nonneg : ∀ s, 0 ≤ rate s
  /-- λ is integrable on every bounded interval, so m(t) is finite -/
  rate_intervalIntegrable : ∀ t, IntervalIntegrable rate volume 0 t
  /-- interarrival times of the underlying unit-rate Poisson process -/
  gap : ℕ → Ω → ℝ
  /-- the random mark of the `k`-th demand, which determines its resupply time -/
  mark : ℕ → Ω → E
  /-- the common law of the marks -/
  markLaw : Measure E
  markLaw_isProb : IsProbabilityMeasure markLaw
  /-- `resupply s e`: the resupply time of a unit demanded at time `s` with mark `e` -/
  resupply : ℝ → E → ℝ
  resupply_measurable : Measurable (Function.uncurry resupply)
  resupply_nonneg : ∀ s e, 0 ≤ resupply s e
  /-- resupply times have finite (time-dependent) expectations -/
  resupply_integrable : ∀ s, 0 ≤ s → Integrable (resupply s) markLaw
  gap_measurable : ∀ k, Measurable (gap k)
  mark_measurable : ∀ k, Measurable (mark k)
  /-- the gap is exponential(1), the mark has law `markLaw`, and the two are independent -/
  pair_law : ∀ k, P.map (fun ω => (gap k ω, mark k ω)) = (expMeasure 1).prod markLaw
  /-- the pairs `(gap k, mark k)` are mutually independent across `k` -/
  pair_indep : iIndepFun (fun k ω => (gap k ω, mark k ω)) P

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : Type*} [MeasurableSpace E]

/-- The mean function `m(t) = ∫₀ᵗ λ(s) ds`, the expected number of demands in `[0, t]`. -/
noncomputable def ResupplySystem.meanFn (S : ResupplySystem Ω P E) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, S.rate s

/-- `Γ_k = gap 0 + ⋯ + gap k`, the `k`-th point (from `0`) of the unit-rate Poisson process. -/
noncomputable def ResupplySystem.unitPoint (S : ResupplySystem Ω P E) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), S.gap i ω

/-- The epoch `T_k = inf {s ≥ 0 : m(s) ≥ Γ_k}` of the `k`-th demand. Only demands with
`Γ_k ≤ m(t)` are ever used at time `t`; for them the set is nonempty and `T_k ≤ t`. -/
noncomputable def ResupplySystem.epoch (S : ResupplySystem Ω P E) (k : ℕ) (ω : Ω) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ S.unitPoint k ω ≤ S.meanFn s}

/-- `N(t)`: the number of demands in `[0, t]`, i.e. `#{k : Γ_k ≤ m(t)}` (`0` on the null event
where this set is infinite). -/
noncomputable def ResupplySystem.demandCount (S : ResupplySystem Ω P E) (t : ℝ) (ω : Ω) : ℕ :=
  {k : ℕ | S.unitPoint k ω ≤ S.meanFn t}.ncard

/-- The resupply time `L_k = resupply(T_k, mark_k)` of the unit demanded by the `k`-th demand. -/
noncomputable def ResupplySystem.resupplyTime (S : ResupplySystem Ω P E) (k : ℕ) (ω : Ω) : ℝ :=
  S.resupply (S.epoch k ω) (S.mark k ω)

/-- `X(t)`: the number of units in resupply at time `t`, i.e. the number of demands in `[0, t]`
whose resupply is not complete at time `t` (`t < T_k + L_k`). -/
noncomputable def ResupplySystem.unitsInResupply (S : ResupplySystem Ω P E) (t : ℝ) (ω : Ω) : ℕ :=
  {k : ℕ | S.unitPoint k ω ≤ S.meanFn t ∧ t < S.epoch k ω + S.resupplyTime k ω}.ncard

/-- `G_s(w)`: the probability that a unit demanded at time `s` is resupplied within `w` time
units (by time `s + w`). -/
noncomputable def ResupplySystem.resupplyCdf (S : ResupplySystem Ω P E) (s w : ℝ) : ℝ :=
  (S.markLaw {e | S.resupply s e ≤ w}).toReal

/-- `α(t) = ∫₀ᵗ (1 − G_s(t − s)) λ(s) ds`, the mean number of units in resupply at time `t`. -/
noncomputable def ResupplySystem.alpha (S : ResupplySystem Ω P E) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, (1 - S.resupplyCdf s (t - s)) * S.rate s

/-- Theorem 12's distribution function `F(x) = m(x)/m(t)` for `0 ≤ x < t`, `F(x) = 1` for
`x ≥ t` (and `F(x) = 0` for `x < 0`, since demands occur at nonnegative times). -/
noncomputable def ResupplySystem.arrivalCdf (S : ResupplySystem Ω P E) (t x : ℝ) : ℝ :=
  if x < 0 then 0 else if x < t then S.meanFn x / S.meanFn t else 1

end ServiceParts.NonstatPalm
