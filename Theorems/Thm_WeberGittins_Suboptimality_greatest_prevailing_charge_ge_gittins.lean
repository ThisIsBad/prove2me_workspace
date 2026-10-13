import Definitions.Def_GittinsChargeInterleaving

open BanditAlgorithm

namespace WeberGittins.Suboptimality
theorem greatest_prevailing_charge_ge_gittins {k : ℕ} (H : Fin k → ℕ → ℝ)
    (hH : ∀ i, Antitone (H i)) (astar : ℕ → Fin k)
    (hastar : IsGreedyChargeStackInterleaving H astar) (a : ℕ → Fin k) (t : ℕ) :
    (⨆ i : Fin k, H i (stackPullCountBefore astar i t)) ≤
      ⨆ i : Fin k, H i (stackPullCountBefore a i t) := by sorry
end WeberGittins.Suboptimality

