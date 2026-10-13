import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Definitions.Def_SendSplit_Existence_AugmentedGraph

namespace SendSplit.Existence

theorem six_implies_seven_bounds {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) (r : Fin n → ℝ) (S : Finset (Fin n))
    (hS : IsSinkSelection G S) (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ)
    (hext : ∀ p ∈ G.A, ¬ SameComponent G p.1 p.2 →
      b p.1 p.2 * (∑ i, max (r i) 0) ≤ c p.1 p.2 (∑ i, max (r i) 0))
    (h6 : ∀ u, HasMinCostChain G S (augCost G c b bν) u) :
    (∀ x, IsFlow G r x → ∀ p ∈ G.A,
        augCost G c b bν (some p.1) (some p.2) * ((x p.1 p.2 : ℝ) : EReal)
          ≤ ((c p.1 p.2 (x p.1 p.2) : ℝ) : EReal)) ∧
      (∀ i, minChainCost G S (augCost G c b bν) i ≠ ⊥ ∧
        minChainCost G S (augCost G c b bν) i ≠ ⊤) ∧
      ∀ p ∈ G.A, minChainCost G S (augCost G c b bν) p.1
        ≤ augCost G c b bν (some p.1) (some p.2) + minChainCost G S (augCost G c b bν) p.2 := by sorry

end SendSplit.Existence

