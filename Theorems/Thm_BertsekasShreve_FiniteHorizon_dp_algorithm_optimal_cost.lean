import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Problem
import Definitions.Def_BertsekasShreve_FiniteHorizon_Assumptions

namespace BertsekasShreve.FiniteHorizon

open Model

/-- Proposition 3.1 (Bertsekas & Shreve 1996, pp. 40–41). Let `J₀ ∈ F` satisfy
`J₀(x) > −∞` for all `x` (eq. (4) of Chapter 2) and let `N` be a positive integer.
(a) Under F.1, if `J_{k,π}(x) < ∞` for all `x ∈ S`, `π ∈ Π`, `k = 1, …, N`, then
`J*_N = T^N(J₀)`.
(b) Under F.2, if `J*_k(x) > −∞` for all `x ∈ S`, `k = 1, …, N`, then `J*_N = T^N(J₀)` and
for every `ε > 0` there is `π_ε ∈ Π` with `J*_N ≤ J_{N,π_ε} ≤ J*_N + ε`. -/
theorem dp_algorithm_optimal_cost {S C : Type*} (m : Model S C) (J₀ : S → EReal)
    (hJ₀ : ∀ x, J₀ x ≠ ⊥) (N : ℕ) (hN : 1 ≤ N) :
    (m.AssumptionF1 →
      (∀ x (π : m.Policy) (k : ℕ), 1 ≤ k → k ≤ N → m.costN J₀ k π x < ⊤) →
      m.optCostN J₀ N = m.T^[N] J₀) ∧
    (m.AssumptionF2 →
      (∀ x (k : ℕ), 1 ≤ k → k ≤ N → m.optCostN J₀ k x ≠ ⊥) →
      m.optCostN J₀ N = m.T^[N] J₀ ∧
        ∀ ε : ℝ, 0 < ε → ∃ π : m.Policy,
          m.optCostN J₀ N ≤ m.costN J₀ N π ∧
            m.costN J₀ N π ≤ fun x => m.optCostN J₀ N x + (ε : EReal)) := by sorry

end BertsekasShreve.FiniteHorizon

