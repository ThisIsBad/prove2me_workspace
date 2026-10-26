import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm
import Definitions.Def_NelderMeadLD_Rate1D_Algorithm

namespace NelderMeadLD.Rate1D

open NelderMeadLD.Conv1D

theorem theorem_4_2 :
    ∀ χ γ : ℝ, 1 < χ → 0 < γ → γ < 1 →
      ∃ M : ℕ,
        ∀ σ : ℝ, 0 < σ → σ < 1 →
        ∀ f : ℝ → ℝ, StrictConvexOn ℝ Set.univ f →
        (∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) →
        ∀ p0 : ℝ × ℝ, IsStart f p0 →
        ∃ K : ℕ, FirstBracket f χ γ σ p0 K ∧
          ∀ k : ℕ, K ≤ k →
            diam (run f 1 χ γ σ p0 (k + M)) ≤ 1 / 2 * diam (run f 1 χ γ σ p0 k) := by sorry

end NelderMeadLD.Rate1D

