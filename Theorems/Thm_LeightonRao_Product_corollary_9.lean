import Mathlib
import Definitions.Def_LeightonRao_Product_Setting

namespace LeightonRao.Product

theorem corollary_9 {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (π : V → ℝ)
    (hπ : IsPMFPWeight π) (hp : 2 ≤ (support π).card) (d : V → V → ℝ)
    (hd : IsDistanceFunction d) :
    (∃ T : Finset V, 2 * ((support π).card : ℝ) ≤ 3 * piSum π T ∧
        HasRadiusLE N d T (1 / (2 * ((support π).card : ℝ) ^ 2))) ∨
    (∃ U : Finset V, 0 < piSum π U ∧ 0 < piSum π Uᶜ ∧
        weightedRatio N π U ≤
          36 * totalWeight N d * Real.logb 2 ((support π).card : ℝ)) := by sorry

end LeightonRao.Product

