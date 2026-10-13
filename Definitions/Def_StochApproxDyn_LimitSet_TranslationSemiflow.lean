import Mathlib

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- The translation `Θ^t(Y)(s) = Y(t + s)` on `C⁰(ℝ₊, M)`, `t ≥ 0` (Benaïm 1999, p. 10, on the
nonnegative half-line). -/
def translate {M : Type*} [MetricSpace M] (t : ℝ≥0) (Y : C(ℝ≥0, M)) : C(ℝ≥0, M) :=
  Y.comp ⟨fun s => t + s, continuous_const.add continuous_id⟩

/-- The trajectory `Φ^p : s ↦ Φ_s(p)` of `p`, an element of `C⁰(ℝ₊, M)` (p. 10). -/
def trajectory {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (p : M) : C(ℝ≥0, M) :=
  ⟨fun s => Φ s p, Φ.continuous continuous_id continuous_const⟩

/-- `S_Φ`, the set of all trajectories `Φ^p`, `p ∈ M` (p. 10). -/
def trajectorySpace {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) : Set C(ℝ≥0, M) :=
  Set.range (trajectory Φ)

/-- The retraction `Φ̂(Y) = Φ^{Y(0)}` (p. 10). -/
def retraction {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (Y : C(ℝ≥0, M)) : C(ℝ≥0, M) :=
  trajectory Φ (Y 0)

/-- `d_k(f, g) = sup_{s ∈ [0, k]} d(f(s), g(s))` (p. 10, on the nonnegative half-line). The index
set is nonempty and the supremum is of a continuous function on a compact interval, so it is a
genuine supremum. -/
noncomputable def supDistOn {M : Type*} [MetricSpace M] (k : ℕ) (f g : C(ℝ≥0, M)) : ℝ :=
  ⨆ s : Set.Icc (0 : ℝ≥0) (k : ℝ≥0), dist (f s) (g s)

/-- The distance `d(f, g) = Σ_{k ∈ ℕ} 2^{-k} min(1, d_k(f, g))` on `C⁰(ℝ₊, M)` (p. 10); `k`
starts at `0`. The series is summable since its terms are bounded by `2^{-k}`. -/
noncomputable def uniformCompactDist {M : Type*} [MetricSpace M] (f g : C(ℝ≥0, M)) : ℝ :=
  ∑' k : ℕ, (1 / 2 : ℝ) ^ k * min 1 (supDistOn k f g)

end StochApproxDyn.LimitSet
