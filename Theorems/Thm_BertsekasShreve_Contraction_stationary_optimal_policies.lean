import Mathlib
import Definitions.Def_BertsekasShreve_Contraction_Model
import Definitions.Def_BertsekasShreve_Contraction_AssumptionC

namespace BertsekasShreve.Contraction

open Filter Topology

/-- Proposition 4.3, p. 56. Under Assumption C:
(a) a stationary policy `(μ*, μ*, …)` is optimal (`J_{μ*} = J*`) iff `T_{μ*}(J*) = T(J*)`, and
equivalently iff `T_{μ*}(J_{μ*}) = T(J_{μ*})`;
(b) if for each `x` some policy is optimal at `x`, there is a stationary optimal policy;
(c) for every `ε > 0` there is a stationary policy `(μ_ε, μ_ε, …)` with `‖J* − J_{μ_ε}‖ ≤ ε`. -/
theorem stationary_optimal_policies {S C : Type*} (P : Model S C) (Bbar : Set (BFun S))
    (m : ℕ) (ρ α : ℝ) (hC : AssumptionC P Bbar m ρ α) :
    (∀ μs : P.Selector,
      (P.Jmu μs = P.Jstar ↔ P.Tmu μs P.Jstar = P.T P.Jstar) ∧
      (P.Jmu μs = P.Jstar ↔ P.Tmu μs (P.Jmu μs) = P.T (P.Jmu μs))) ∧
    ((∀ x : S, ∃ π : P.Policy, P.Jpi π x = P.Jstar x) →
      ∃ μs : P.Selector, P.Jmu μs = P.Jstar) ∧
    (∀ ε : ℝ, 0 < ε → ∃ με : P.Selector, SupDistLe P.Jstar (P.Jmu με) ε) := by sorry

end BertsekasShreve.Contraction

