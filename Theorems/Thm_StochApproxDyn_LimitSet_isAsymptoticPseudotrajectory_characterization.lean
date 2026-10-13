import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_LimitSet_TranslationSemiflow

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- Theorem 3.2 (Benaïm 1999, pp. 10–11), on `C⁰(ℝ₊, M)` with the compact-open topology
(uniform convergence on compact intervals). For a continuous `X : ℝ₊ → M` with relatively compact
image: (i) `X` is an asymptotic pseudotrajectory of `Φ` iff (ii) `X` is uniformly continuous and
every limit point `Y = lim_k Θ^{t_k}(X)`, `t_k → ∞`, lies in `S_Φ`; and (i) implies
(iii) `{Θ^t(X)}_{t ≥ 0}` is relatively compact. -/
theorem isAsymptoticPseudotrajectory_characterization {M : Type*} [MetricSpace M]
    (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M)) (hX : IsCompact (closure (Set.range X))) :
    (IsAsymptoticPseudotrajectory Φ X ↔
      (UniformContinuous X ∧
        ∀ Y : C(ℝ≥0, M), (∃ τ : ℕ → ℝ≥0, Filter.Tendsto τ Filter.atTop Filter.atTop ∧
            Filter.Tendsto (fun k => translate (τ k) X) Filter.atTop (nhds Y)) →
          Y ∈ trajectorySpace Φ)) ∧
    (IsAsymptoticPseudotrajectory Φ X →
      IsCompact (closure (Set.range fun t : ℝ≥0 => translate t X))) := by sorry

end StochApproxDyn.LimitSet

