import Mathlib
import Definitions.Def_LeightonRao_Product_Setting

namespace LeightonRao.Product

theorem theorem_7 : ∃ c : ℝ, 0 < c ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (π : V → ℝ),
      IsConnectedNet N → IsPMFPWeight π → 2 ≤ (support π).card →
      c * pmfpMinCut N π / Real.logb 2 ((max (numCommodities π) 2 : ℕ) : ℝ) ≤
          maxFlow N (productDemand π) ∧
        maxFlow N (productDemand π) ≤ pmfpMinCut N π := by sorry

end LeightonRao.Product

