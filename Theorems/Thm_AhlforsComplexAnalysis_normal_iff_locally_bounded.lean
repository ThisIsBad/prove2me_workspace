import Definitions.Def_AhlforsComplexAnalysis_Defs
import Mathlib

open AhlforsComplexAnalysis


theorem AhlforsComplexAnalysis.normal_iff_locally_bounded {Ω : Set ℂ} (hΩ : IsRegion Ω)
    {𝔉 : Set (ℂ → ℂ)} (hanal : ∀ f ∈ 𝔉, AnalyticOnNhd ℂ f Ω) :
    IsNormalFamily 𝔉 Ω ↔
      ∀ K ⊆ Ω, IsCompact K → ∃ M : ℝ, ∀ f ∈ 𝔉, ∀ z ∈ K, ‖f z‖ ≤ M := by sorry

