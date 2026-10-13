import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_LimitSet_Attractor
import Definitions.Def_StochApproxDyn_LimitSet_Invariance

open scoped NNReal ENNReal

namespace StochApproxDyn.Attractor

/-- Positive invariance (p. 20): `Φ_t(A) ⊆ A` for every `t ≥ 0`. -/
def IsPositivelyInvariant {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (A : Set M) : Prop :=
  ∀ t : ℝ≥0, Φ t '' A ⊆ A

/-- `d_X(T) = sup_{k ∈ ℕ} d(Φ_T(X(kT)), X(kT + T))` (p. 28, Eq. (23)), computed in `ℝ≥0∞` so that
an unbounded supremum is `∞` rather than a junk value. -/
noncomputable def stepDeviation {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → M)
    (T : ℝ≥0) : ℝ≥0∞ :=
  ⨆ k : ℕ, edist (Φ T (X (k * T))) (X (k * T + T))

end StochApproxDyn.Attractor
