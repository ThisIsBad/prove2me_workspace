import Mathlib
import Definitions.Def_StochApproxDyn_Interpolation_VectorFieldFlow
import Definitions.Def_StochApproxDyn_Interpolation_Scheme

open scoped NNReal Topology
open Filter

namespace StochApproxDyn.Interpolation

/-- Benaïm 1999, Proposition 4.1, estimate (11), p. 13. Let `F` be continuous and globally
integrable with flow `Φ`. For every `T > 0` and all constants `L ≥ 0`, `K` there is `C` (depending
only on `F`, `T`, `L`, `K`) such that: whenever the standing assumptions on `γ`, the recursion (7)
and A1 hold, and `F` is `L`-Lipschitz and bounded by `K` on the `r`-neighbourhood of
`{x_n : n ≥ 0}` for some `r > 0` (A2′), then for all `t` large enough (with `t ≥ 1`)
`sup_{0≤h≤T} ‖X(t + h) − Φ_h(X(t))‖ ≤ C [Δ(t − 1, T + 1) + sup_{t≤s≤t+T} γ̄(s)]`. -/
theorem shadowing_estimate {d : ℕ}
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hF : Continuous F)
    (hint : IsGloballyIntegrable F)
    (Φ : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hΦ : IsFlowOf F Φ) :
    ∀ T : ℝ, 0 < T → ∀ L : ℝ≥0, ∀ K : ℝ, ∃ C : ℝ,
      ∀ (γ : ℕ → ℝ) (x U : ℕ → EuclideanSpace ℝ (Fin d)) (r : ℝ),
        IsStepSizeSeq γ → SatisfiesScheme F γ x U → SatisfiesA1 γ U → 0 < r →
        LipschitzOnWith L F (Metric.thickening r (Set.range x)) →
        (∀ y ∈ Metric.thickening r (Set.range x), ‖F y‖ ≤ K) →
        ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ h ∈ Set.Icc (0 : ℝ) T,
          ‖interpAffine γ x (t + h) - Φ h (interpAffine γ x t)‖ ≤
            C * (Delta γ U (t - 1) (T + 1) + sSup (stepInterp γ '' Set.Icc t (t + T))) := by sorry

end StochApproxDyn.Interpolation

