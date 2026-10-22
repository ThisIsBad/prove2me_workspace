import Mathlib
import Definitions.Def_LeightonRao_Product_Setting

namespace LeightonRao.Product

theorem lemma_10 {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (hconn : IsConnectedNet N)
    (π : V → ℝ) (hπ : IsPMFPWeight π) (hp : 2 ≤ (support π).card) (d : V → V → ℝ)
    (hd : IsDistanceFunction d) (T : Finset V)
    (hT : 2 * ((support π).card : ℝ) ≤ 3 * piSum π T)
    (hsum : 1 / (2 * ((support π).card : ℝ)) ≤ ∑ u ∈ Tᶜ, π u * distFrom N d T u) :
    ∃ U : Finset V, 0 < piSum π U ∧ 0 < piSum π Uᶜ ∧
      weightedRatio N π U ≤ 6 * totalWeight N d := by sorry

end LeightonRao.Product

