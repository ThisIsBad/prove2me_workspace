import Definitions.Def_AhlforsComplexAnalysis_Defs
import Mathlib

open AhlforsComplexAnalysis


theorem AhlforsComplexAnalysis.hurwitz {Ω : Set ℂ} (hΩ : IsRegion Ω) {F : ℕ → ℂ → ℂ}
    {f : ℂ → ℂ} (hF : ∀ n, AnalyticOnNhd ℂ (F n) Ω) (hF0 : ∀ n, ∀ z ∈ Ω, F n z ≠ 0)
    (hconv : ∀ K ⊆ Ω, IsCompact K → TendstoUniformlyOn F f Filter.atTop K) :
    (∀ z ∈ Ω, f z = 0) ∨ (∀ z ∈ Ω, f z ≠ 0) := by sorry

