import Definitions.Def_AhlforsComplexAnalysis_Defs
import Mathlib

open AhlforsComplexAnalysis

theorem AhlforsComplexAnalysis.exists_log_and_root {Ω : Set ℂ}
    (hΩ : IsSimplyConnectedRegion Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    (∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L Ω ∧ ∀ z ∈ Ω, Complex.exp (L z) = f z) ∧
    ∀ n : ℕ, 0 < n → ∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R Ω ∧ ∀ z ∈ Ω, R z ^ n = f z := by sorry
