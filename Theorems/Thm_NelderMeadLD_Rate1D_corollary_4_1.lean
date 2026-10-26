import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm
import Definitions.Def_NelderMeadLD_Rate1D_Algorithm

namespace NelderMeadLD.Rate1D

open NelderMeadLD.Conv1D

theorem corollary_4_1 (χ γ σ : ℝ) (hpar : ParamsOK 1 χ γ σ)
    (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (p0 : ℝ × ℝ) (h0 : IsStart f p0)
    (K : ℕ) (hK : FirstBracket f χ γ σ p0 K) :
    ∃ k : ℕ, K ≤ k ∧ k ≤ K + rStar χ ∧ IsContraction (moveAt f χ γ σ p0 k) := by sorry

end NelderMeadLD.Rate1D

