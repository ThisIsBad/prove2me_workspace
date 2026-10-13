import Definitions.Def_LambdaCoalescent_Rates_Setting

namespace LambdaCoalescent.Rates

open MeasureTheory

/-- Lemma 18, p. 1882: formula (1) is a bijection. -/
theorem lemma_18_bijection :
    (∀ Λ : Measure ℝ, IsFiniteMeasure Λ → Λ (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
      Consistent (lamOf Λ)) ∧
    (∀ lam : ℕ → ℕ → ℝ,
      (∀ b k, 2 ≤ k → k ≤ b → 0 ≤ lam b k) →
      Consistent lam →
      ∃! Λ : Measure ℝ,
        IsFiniteMeasure Λ ∧ Λ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
          ∀ b k, 2 ≤ k → k ≤ b → lam b k = lamOf Λ b k) := by sorry

end LambdaCoalescent.Rates

