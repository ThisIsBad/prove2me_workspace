import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm
import Definitions.Def_NelderMeadLD_Rate1D_Algorithm

namespace NelderMeadLD.Rate1D

open NelderMeadLD.Conv1D

theorem lemma_4_8 :
    ∀ χ γ : ℝ, 1 < χ → 0 < γ → γ < 1 →
      ∃ φ : ℝ, φ < 1 ∧
        ∀ σ : ℝ, 0 < σ → σ < 1 →
        ∀ f : ℝ → ℝ, StrictConvexOn ℝ Set.univ f →
        (∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) →
        ∀ p0 : ℝ × ℝ, IsStart f p0 →
        ∀ k k' : ℕ, k < k' →
          IsContraction (moveAt f χ γ σ p0 k) →
          IsContraction (moveAt f χ γ σ p0 k') →
          (∀ i : ℕ, k < i → i < k' → ¬ IsContraction (moveAt f χ γ σ p0 i)) →
          diam (run f 1 χ γ σ p0 (k' + 1)) ≤ φ * diam (run f 1 χ γ σ p0 (k + 1)) := by sorry

end NelderMeadLD.Rate1D

