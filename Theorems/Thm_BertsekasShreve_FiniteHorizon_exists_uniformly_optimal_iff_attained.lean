import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Problem

namespace BertsekasShreve.FiniteHorizon

open Model

/-- Corollary 3.3.1 (Bertsekas & Shreve 1996, p. 45).
(a) A uniformly `N`-stage optimal policy exists if and only if the infimum in
`T^{k+1}(J₀)(x) = inf_{u ∈ U(x)} H[x, u, T^k(J₀)]` (eq. (15) of Chapter 3) is attained for each
`x ∈ S` and `k = 0, 1, …, N − 1`.
(b) If a uniformly `N`-stage optimal policy exists, then `J*_N = T^N(J₀)`. -/
theorem exists_uniformly_optimal_iff_attained {S C : Type*} (m : Model S C) (J₀ : S → EReal)
    (hJ₀ : ∀ x, J₀ x ≠ ⊥) (N : ℕ) (hN : 1 ≤ N) :
    ((∃ π : m.Policy, m.IsUniformlyNStageOptimal J₀ N π) ↔
      ∀ x, ∀ k, k < N → ∃ u ∈ m.U x, m.H x u (m.T^[k] J₀) = m.T^[k + 1] J₀ x) ∧
    ((∃ π : m.Policy, m.IsUniformlyNStageOptimal J₀ N π) →
      m.optCostN J₀ N = m.T^[N] J₀) := by sorry

end BertsekasShreve.FiniteHorizon

