import Mathlib
import Definitions.Def_LeightonRao_Product_Setting

namespace LeightonRao.Product

theorem lp_duality {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (hconn : IsConnectedNet N)
    (π : V → ℝ) (hπ : IsPMFPWeight π) (hp : 2 ≤ (support π).card) :
    (∀ d : V → V → ℝ, IsDistanceFunction d → SatisfiesPMFPConstraint N π d →
        maxFlow N (productDemand π) ≤ totalWeight N d) ∧
    (∃ d : V → V → ℝ, IsDistanceFunction d ∧ SatisfiesPMFPConstraint N π d ∧
        totalWeight N d = maxFlow N (productDemand π)) := by sorry

end LeightonRao.Product

