import Mathlib
import Definitions.Def_WeightedMajority_Shifting_WML

namespace WeightedMajority.Shifting

theorem lemma_3_1 {n T : ℕ} (hn : 0 < n) {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2)
    (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool) (w : ℕ → Fin n → ℝ) (lam : Fin T → Bool)
    (hrun : IsWMLRun β γ x ρ w lam)
    (hfloor : ∀ i, β * γ / (n : ℝ) * totalWeight (w 0) ≤ w 0 i) :
    (masterMistakes ρ lam : ℝ) ≤
        (Real.log ((n : ℝ) / (β * γ)) + (bestMistakesOn x ρ 0 T : ℝ) * Real.log (1 / β)) /
          Real.log (1 / uFactor β γ) ∧
      ∀ i, β * γ / (n : ℝ) * totalWeight (w T) ≤ w T i := by sorry

end WeightedMajority.Shifting

