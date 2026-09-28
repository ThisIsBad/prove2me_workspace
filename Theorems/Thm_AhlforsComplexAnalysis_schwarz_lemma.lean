import Definitions.Def_AhlforsComplexAnalysis_Defs
import Mathlib

open AhlforsComplexAnalysis


theorem AhlforsComplexAnalysis.schwarz_lemma {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    (hbound : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ 1) (h0 : f 0 = 0) :
    (∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ ‖z‖) ∧ ‖deriv f 0‖ ≤ 1 ∧
    (((∃ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 ∧ ‖f z‖ = ‖z‖) ∨ ‖deriv f 0‖ = 1) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, f z = c * z) := by sorry

