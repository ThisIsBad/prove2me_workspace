import Definitions.Def_AhlforsComplexAnalysis_Defs
import Mathlib

open AhlforsComplexAnalysis


theorem AhlforsComplexAnalysis.disk_map_is_linear_transformation {a b : ℂ} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball a r))
    (hinj : Set.InjOn f (Metric.ball a r)) (honto : f '' Metric.ball a r = Metric.ball b s) :
    ∃ α β γ δ : ℂ, α * δ - β * γ ≠ 0 ∧
      ∀ z ∈ Metric.ball a r, γ * z + δ ≠ 0 ∧ f z = (α * z + β) / (γ * z + δ) := by sorry

