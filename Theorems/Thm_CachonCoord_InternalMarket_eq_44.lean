import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue

namespace CachonCoord.InternalMarket

/-- Eq. (44), §6.9.1, p. 93 (Cachon 2003, 3rd draft): for demand realizations `α₁, α₂ > 0`,
elasticity `η > 1` and output `Q > 0`, total retailer revenue `γ ↦ π(γ, α, Q)` is strictly
concave on `[0, 1]`, and the share `γ°(α) = α₁^η / (α₁^η + α₂^η)` lies in `[0, 1]` and is its unique
maximizer there. -/
theorem eq_44 (η α₁ α₂ Q : ℝ) (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hQ : 0 < Q) :
    StrictConcaveOn ℝ (Set.Icc 0 1) (fun γ => revenue η α₁ α₂ γ Q) ∧
    optShare η α₁ α₂ ∈ Set.Icc (0 : ℝ) 1 ∧
    IsMaxOn (fun γ => revenue η α₁ α₂ γ Q) (Set.Icc 0 1) (optShare η α₁ α₂) ∧
    ∀ γ ∈ Set.Icc (0 : ℝ) 1,
      IsMaxOn (fun γ' => revenue η α₁ α₂ γ' Q) (Set.Icc 0 1) γ → γ = optShare η α₁ α₂ := by sorry

end CachonCoord.InternalMarket

