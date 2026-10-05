import Mathlib
import Definitions.Def_BertsekasShreve_Contraction_Model
import Definitions.Def_BertsekasShreve_Contraction_AssumptionC

namespace BertsekasShreve.Contraction

open Filter Topology

/-- Proposition 4.2, p. 55. Under Assumption C:
(a) `J* ∈ B̄`, `J* = T(J*)`, and `J*` is the only fixed point of `T` in `B̄`; if `J' ∈ B̄` and
`T(J') ≤ J'` then `J* ≤ J'`, while if `J' ≤ T(J')` then `J' ≤ J*`;
(b) for every `μ ∈ M`, `J_μ ∈ B̄` and `J_μ` is the unique fixed point of `T_μ` in `B̄`;
(c) `‖T^N(J) − J*‖ → 0` and `‖T_μ^N(J) − J_μ‖ → 0` for every `J ∈ B̄`, `μ ∈ M`. -/
theorem optimal_cost_unique_fixed_point {S C : Type*} (P : Model S C) (Bbar : Set (BFun S))
    (m : ℕ) (ρ α : ℝ) (hC : AssumptionC P Bbar m ρ α) :
    ((∃ Js ∈ Bbar, P.Jstar = toF Js) ∧
      P.T P.Jstar = P.Jstar ∧
      (∀ J ∈ Bbar, P.T (toF J) = toF J → toF J = P.Jstar) ∧
      (∀ J ∈ Bbar, P.T (toF J) ≤ toF J → P.Jstar ≤ toF J) ∧
      (∀ J ∈ Bbar, toF J ≤ P.T (toF J) → toF J ≤ P.Jstar)) ∧
    (∀ μ : P.Selector,
      (∃ Jm ∈ Bbar, P.Jmu μ = toF Jm) ∧
      P.Tmu μ (P.Jmu μ) = P.Jmu μ ∧
      (∀ J ∈ Bbar, P.Tmu μ (toF J) = toF J → toF J = P.Jmu μ)) ∧
    ((∀ J ∈ Bbar, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
        SupDistLe (P.T^[N] (toF J)) P.Jstar ε) ∧
      (∀ μ : P.Selector, ∀ J ∈ Bbar, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
        SupDistLe ((P.Tmu μ)^[N] (toF J)) (P.Jmu μ) ε)) := by sorry

end BertsekasShreve.Contraction

