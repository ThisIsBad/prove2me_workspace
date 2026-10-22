import Mathlib
import Definitions.Def_NetworkControl_CapacityRegion_QueueBacklog
import Definitions.Def_NetworkControl_CapacityRegion_StronglyStable


namespace NetworkControl.CapacityRegion

open MeasureTheory

/-- Lemma 3.3 (Necessary Condition for Strong Stability), Georgiadis–Neely–Tassiulas p. 24.
Let `U(t)` be the backlog of a queue `U(t+1) = max[U(t) - μ(t), 0] + A(t)` with nonnegative
arrivals `A(t)`, nonnegative service `μ(t)` and nonnegative initial backlog `U(0)` of finite mean.
If the queue is strongly stable, and either `E A(t) ≤ Amax` for all `t` or
`E{μ(t) - A(t)} ≤ Dmax` for all `t` (with `Amax, Dmax` finite), then `E U(t)/t → 0`.

Corrected version: `U` is the backlog process of the queue (`QueueBacklog`), not a free real
sequence — the retired version lost the queueing law (and the nonnegativity of backlogs) that
links `U` to `A` and `μ`, so the arrival/service bounds constrained nothing. -/
theorem lemma_necessary_condition_strong_stability_v2
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (A svc : ℕ → Ω → ℝ) (U0 : Ω → ℝ)
    (hAnn : ∀ t ω, 0 ≤ A t ω) (hsvcnn : ∀ t ω, 0 ≤ svc t ω) (hU0nn : ∀ ω, 0 ≤ U0 ω)
    (hU0int : Integrable U0 P) (hAint : ∀ t, Integrable (A t) P)
    (hsvcint : ∀ t, Integrable (svc t) P)
    (Amax Dmax : ℝ) (hAmax : 0 ≤ Amax) (hDmax : 0 ≤ Dmax)
    (hstable : StronglyStable (fun t : ℕ => ∫ ω, QueueBacklog A svc U0 t ω ∂P))
    (hbound : (∀ t : ℕ, ∫ ω, A t ω ∂P ≤ Amax) ∨
      (∀ t : ℕ, ∫ ω, (svc t ω - A t ω) ∂P ≤ Dmax)) :
    Filter.Tendsto (fun t : ℕ => (∫ ω, QueueBacklog A svc U0 t ω ∂P) / (t : ℝ))
      Filter.atTop (nhds 0) := by sorry

end NetworkControl.CapacityRegion

