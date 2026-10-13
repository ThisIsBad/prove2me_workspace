import Mathlib

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- An *asymptotic pseudotrajectory* of the semiflow `Φ` (Benaïm 1999, p. 9): a continuous
`X : ℝ₊ → M` with `lim_{t→∞} sup_{0 ≤ h ≤ T} d(X(t+h), Φ_h(X(t))) = 0` for every `T > 0`,
written with `ε`: for all `T > 0` and `ε > 0` there is `t₀` such that
`d(X(t+h), Φ_h(X(t))) < ε` for all `t ≥ t₀` and `0 ≤ h ≤ T`. -/
def IsAsymptoticPseudotrajectory {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → M) :
    Prop :=
  Continuous X ∧
    ∀ T : ℝ≥0, 0 < T → ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t → ∀ h : ℝ≥0, h ≤ T →
      dist (X (t + h)) (Φ h (X t)) < ε

/-- The limit set `L(X) = ⋂_{t ≥ 0} closure (X([t, ∞)))` (p. 24). -/
def limitSet {M : Type*} [MetricSpace M] (X : ℝ≥0 → M) : Set M :=
  ⋂ t : ℝ≥0, closure (X '' Set.Ici t)

end StochApproxDyn.LimitSet
