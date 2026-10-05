import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Problem
import Definitions.Def_BertsekasShreve_FiniteHorizon_Assumptions

namespace BertsekasShreve.FiniteHorizon

open Filter Topology Model

/-- Proposition 3.2 (Bertsekas & Shreve 1996, p. 43). Let F.3 hold, `J₀(x) > −∞` for all `x`,
`N ≥ 1`, and `J_{k,π}(x) < ∞` for all `x ∈ S`, `π ∈ Π`, `k = 1, …, N`. Then
`J*_N = T^N(J₀)`; for every sequence of positive numbers `ε_n ↓ 0` there is a sequence of
policies exhibiting `{ε_n}`-dominated convergence to optimality; and if in addition
`J*_N(x) > −∞` for all `x`, then for every `ε > 0` there is an `N`-stage `ε`-optimal policy. -/
theorem dp_optimal_cost_of_F3 {S C : Type*} (m : Model S C) (J₀ : S → EReal)
    (hJ₀ : ∀ x, J₀ x ≠ ⊥) (N : ℕ) (hN : 1 ≤ N) (hF3 : m.AssumptionF3)
    (hfin : ∀ x (π : m.Policy) (k : ℕ), 1 ≤ k → k ≤ N → m.costN J₀ k π x < ⊤) :
    m.optCostN J₀ N = m.T^[N] J₀ ∧
    (∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Antitone ε → Tendsto ε atTop (𝓝 0) →
      ∃ πs : ℕ → m.Policy, m.IsDominatedConvergence J₀ N ε πs) ∧
    ((∀ x, m.optCostN J₀ N x ≠ ⊥) →
      ∀ ε : ℝ, 0 < ε → ∃ π : m.Policy, m.IsNStageEpsOptimal J₀ N ε π) := by sorry

end BertsekasShreve.FiniteHorizon

