import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Problem

namespace BertsekasShreve.FiniteHorizon

open Model

/-- Proposition 3.4 (Bertsekas & Shreve 1996, p. 46). Let the control space `C` be a Hausdorff
space and assume that for each `x ∈ S`, `λ ∈ R` and `k = 0, 1, …, N − 1` the set
`U_k(x, λ) = {u ∈ U(x) | H[x, u, T^k(J₀)] ≤ λ}` (eq. (16) of Chapter 3) is compact. Then
`J*_N = T^N(J₀)` and there exists a uniformly `N`-stage optimal policy. -/
theorem compact_sublevel_uniformly_optimal {S C : Type*} [TopologicalSpace C] [T2Space C]
    (m : Model S C) (J₀ : S → EReal) (hJ₀ : ∀ x, J₀ x ≠ ⊥) (N : ℕ) (hN : 1 ≤ N)
    (hcpt : ∀ x (lam : ℝ) (k : ℕ), k < N →
      IsCompact {u | u ∈ m.U x ∧ m.H x u (m.T^[k] J₀) ≤ (lam : EReal)}) :
    m.optCostN J₀ N = m.T^[N] J₀ ∧ ∃ π : m.Policy, m.IsUniformlyNStageOptimal J₀ N π := by sorry

end BertsekasShreve.FiniteHorizon

