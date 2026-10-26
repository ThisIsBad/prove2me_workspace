import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm
import Definitions.Def_NelderMeadLD_Rate1D_Algorithm

namespace NelderMeadLD.Rate1D

open NelderMeadLD.Conv1D

theorem lemma_4_6 (χ γ σ : ℝ) (hpar : ParamsOK 1 χ γ σ)
    (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (p0 : ℝ × ℝ) (h0 : IsStart f p0) :
    (∀ k : ℕ, ¬ ∀ i < rStar χ + 1, moveAt f χ γ σ p0 (k + i) = Move.reflect) ∧
    (∀ k : ℕ, moveAt f χ γ σ p0 k = Move.reflect →
      moveAt f χ γ σ p0 (k + 1) ≠ Move.expand) := by sorry

end NelderMeadLD.Rate1D

