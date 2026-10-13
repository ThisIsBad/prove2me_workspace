import Mathlib

open scoped NNReal Topology
open Filter

namespace StochApproxDyn.Interpolation

/-- An *asymptotic pseudotrajectory* (Benaïm 1999, §3, p. 9): a continuous `X : ℝ₊ → M` such that
for every `T > 0`, `lim_{t → ∞} sup_{0 ≤ h ≤ T} d(X(t + h), Φ_h(X(t))) = 0`. The dynamics
`Φ : ℝ → M → M` is a flow or (through its values at `h ≥ 0`) a semiflow; only `Φ_h` with
`h ≥ 0` is used. The limit is written with `ε`: for all `T > 0` and `ε > 0` there is `t₀` with
`d(X(t + h), Φ_h(X(t))) < ε` for all `t ≥ t₀` and `0 ≤ h ≤ T`. -/
def IsAsymptoticPseudotrajectory {M : Type*} [MetricSpace M] (Φ : ℝ → M → M) (X : ℝ≥0 → M) :
    Prop :=
  Continuous X ∧
    ∀ T : ℝ≥0, 0 < T → ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t → ∀ h : ℝ≥0, h ≤ T →
      dist (X (t + h)) (Φ (h : ℝ) (X t)) < ε

/-- The translate `Θ^t(X) ∈ C⁰(ℝ, M)`, `Θ^t(X)(s) = X(t + s)` (p. 10), where `X : ℝ₊ → M` is
extended to `ℝ` by `X(s) = X(0)` for `s < 0`; `Real.toNNReal` performs this extension. -/
def translate {M : Type*} [MetricSpace M] (X : C(ℝ≥0, M)) (t : ℝ≥0) : C(ℝ, M) :=
  ⟨fun s => X (Real.toNNReal ((t : ℝ) + s)),
    X.continuous.comp (continuous_real_toNNReal.comp (continuous_const.add continuous_id))⟩

/-- The trajectory `Φ^p : s ↦ Φ_s(p)` of a point `p` under a flow `Φ`, an element of
`C⁰(ℝ, M)` (p. 10). -/
def trajectory {M : Type*} [MetricSpace M] (Φ : Flow ℝ M) (p : M) : C(ℝ, M) :=
  ⟨fun s => Φ s p, Φ.continuous continuous_id continuous_const⟩

/-- `S_Φ ⊆ C⁰(ℝ, M)`, the set of all trajectories `Φ^p`, `p ∈ M` (p. 10). An element `Y` lies in
`S_Φ` iff it is a fixed point of the retraction `Φ̂(Y) = Φ^{Y(0)}`. -/
def trajectorySet {M : Type*} [MetricSpace M] (Φ : Flow ℝ M) : Set C(ℝ, M) :=
  Set.range (trajectory Φ)

/-- `Y` is a *limit point of `{Θ^t(X)}`* (p. 10, footnote 1): `Y` is the limit in `C⁰(ℝ, M)`
(compact-open topology, i.e. uniform convergence on compact intervals) of a sequence
`Θ^{t_k}(X)` with `t_k → ∞`. -/
def IsLimitPointOfTranslates {M : Type*} [MetricSpace M] (X : C(ℝ≥0, M)) (Y : C(ℝ, M)) : Prop :=
  ∃ t : ℕ → ℝ≥0, Tendsto t atTop atTop ∧ Tendsto (fun k => translate X (t k)) atTop (𝓝 Y)

end StochApproxDyn.Interpolation
