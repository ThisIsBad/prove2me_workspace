import Mathlib
import Definitions.Def_BertsekasShreve_Generalized_Model
import Definitions.Def_BertsekasShreve_Generalized_Assumptions
import Definitions.Def_BertsekasShreve_Generalized_Optimality

namespace BertsekasShreve.Generalized

open Filter Topology

/-- Proposition 6.5(a), p. 97. Under A.1–A.5, Assumption C̃ and the exact selection assumption,
if for each `x ∈ S` there is a policy in `Π̃` which is optimal at `x`, then there is an optimal
stationary policy in `Π̃`. -/
theorem prop6_5a_pointwise_optimal_stationary {S C : Type*} (P : Model S C)
    (hA1 : P.A1) (hA2 : P.A2) (hA3 : P.A3) (hA4 : P.A4) (hA5 : P.A5)
    (Bbar : Set (BertsekasShreve.Contraction.BFun S)) (m : ℕ) (ρ α : ℝ) (hC : P.AssumptionCtilde Bbar m ρ α)
    (hES : P.ExactSelection)
    (hopt : ∀ x, ∃ π : P.Policy, P.IsOptimalAt π x) :
    ∃ μ : P.Sel, P.IsOptimal (P.stationary μ) := by sorry

end BertsekasShreve.Generalized

