import Definitions.Def_LambdaCoalescent_Rates_Setting

namespace LambdaCoalescent.Rates

/-- Lemma 18, p. 1882, equivalence (22). -/
theorem lemma_18_consistent_iff (lam : ℕ → ℕ → ℝ)
    (hlam : ∀ b k, 2 ≤ k → k ≤ b → 0 ≤ lam b k) :
    Consistent lam ↔
      ∀ b k, 2 ≤ k → k ≤ b →
        lam b k = lam (b + 1) k + lam (b + 1) (k + 1) := by sorry

end LambdaCoalescent.Rates

