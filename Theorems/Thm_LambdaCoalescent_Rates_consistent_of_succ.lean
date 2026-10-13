import Definitions.Def_LambdaCoalescent_Rates_Setting

namespace LambdaCoalescent.Rates

open MeasureTheory

/-- Proof of Lemma 18, p. 1882: checking one added label suffices. -/
theorem consistent_of_succ (lam : ℕ → ℕ → ℝ)
    (hlam : ∀ b k, 2 ≤ k → k ≤ b → 0 ≤ lam b k)
    (hsucc : ∀ (n : ℕ) (π : Setoid (Fin (n + 1))) (σ : Setoid (Fin n))
      (t : ℝ), 0 ≤ t →
        (∑ π' : Setoid (Fin (n + 1)),
          if restrictLE (Nat.le_succ n) π' = σ then
            NormedSpace.exp (t • rateMatrix lam (n + 1)) π π' else 0) =
        NormedSpace.exp (t • rateMatrix lam n)
          (restrictLE (Nat.le_succ n) π) σ) :
    Consistent lam := by sorry

end LambdaCoalescent.Rates

