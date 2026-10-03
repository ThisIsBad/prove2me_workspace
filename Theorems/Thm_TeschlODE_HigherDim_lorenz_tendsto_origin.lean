import Mathlib
import Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve
import Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow
import Definitions.Def_TeschlODE_HigherDim_lorenzField

namespace TeschlODE.HigherDim

/-- Teschl, Lemma 8.7, p. 235: for the Lorenz equation (8.13) with `σ, r, b > 0` and `r ≤ 1`,
the origin is the only fixed point, and every solution exists for all `t ≥ 0` and converges to
the origin as `t → ∞`. -/
theorem lorenz_tendsto_origin (σ r b : ℝ) (hσ : 0 < σ) (hr : 0 < r) (hb : 0 < b)
    (hr1 : r ≤ 1) :
    (∀ v : EuclideanSpace ℝ (Fin 3), lorenzField σ r b v = 0 ↔ v = 0) ∧
      ∀ (I : EuclideanSpace ℝ (Fin 3) → Set ℝ)
        (Φ : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
        IsMaximalFlow (lorenzField σ r b) Set.univ I Φ →
          ∀ x : EuclideanSpace ℝ (Fin 3), Set.Ici (0 : ℝ) ⊆ I x ∧
            Filter.Tendsto (fun t => Φ t x) Filter.atTop (nhds 0) := by sorry

end TeschlODE.HigherDim

