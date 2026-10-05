import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Problem

namespace BertsekasShreve.FiniteHorizon

open Model

/-- Proposition 3.3 (Bertsekas & Shreve 1996, p. 44). Under the Monotonicity Assumption only,
a policy `π* = (μ₀*, μ₁*, …)` is uniformly `N`-stage optimal if and only if
`(T_{μ_k*} T^{N−k−1})(J₀) = T^{N−k}(J₀)` for `k = 0, …, N − 1` (eq. (14) of Chapter 3). -/
theorem uniformly_optimal_iff {S C : Type*} (m : Model S C) (J₀ : S → EReal)
    (hJ₀ : ∀ x, J₀ x ≠ ⊥) (N : ℕ) (hN : 1 ≤ N) (π : m.Policy) :
    m.IsUniformlyNStageOptimal J₀ N π ↔
      ∀ k, k < N → m.Tmu (π k) (m.T^[N - k - 1] J₀) = m.T^[N - k] J₀ := by sorry

end BertsekasShreve.FiniteHorizon

