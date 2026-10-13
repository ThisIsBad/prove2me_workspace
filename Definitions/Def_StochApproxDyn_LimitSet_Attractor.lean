import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_Invariance

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- An *attractor* (Benaïm 1999, p. 22): `A` is nonempty, compact and invariant (`Φ_t A = A`),
and has a neighbourhood `W` such that `dist(Φ_t x, A) → 0` as `t → ∞` uniformly in `x ∈ W`. -/
def IsAttractor {X : Type*} [MetricSpace X] (Φ : Flow ℝ≥0 X) (A : Set X) : Prop :=
  A.Nonempty ∧ IsCompact A ∧ IsInvariantSet Φ A ∧
    ∃ W ∈ nhdsSet A, ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t → ∀ x ∈ W,
      Metric.infDist (Φ t x) A < ε

/-- The basin of `A`: all points `x` with `dist(Φ_t x, A) → 0` as `t → ∞`. -/
def basin {X : Type*} [MetricSpace X] (Φ : Flow ℝ≥0 X) (A : Set X) : Set X :=
  {x | Filter.Tendsto (fun t : ℝ≥0 => Metric.infDist (Φ t x) A) Filter.atTop (nhds 0)}

end StochApproxDyn.LimitSet
