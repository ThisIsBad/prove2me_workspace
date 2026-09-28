import Mathlib

namespace ScenarioReduction.BinaryTree

/-- Branch index at tree level `k` (paper's `i_k - 1 ∈ {0, 1}`) of the scenario indexed by
`σ : Fin K → Fin 2`: Fin-index `r` stores level `r + 1`, so level `k ∈ {1, …, K}` is `σ ⟨k - 1, _⟩`.
Level `0` (the root, which carries no choice) and levels above `K` return the default `0`;
they are never used with a nonzero weight. -/
def lev {K : ℕ} (σ : Fin K → Fin 2) (k : ℕ) : Fin 2 :=
  if h : 1 ≤ k ∧ k ≤ K then σ ⟨k - 1, by omega⟩ else 0

/-- Scenario `ω_σ = (ω^0, …, ω^K) ∈ ℝ^{K+1}` of the regular binary tree, eq. (19):
`ω^k = ∑_{j=1}^{k} δ^j_{i_j}` with `δ^j_{i_j} = (2 i_j - 3) δ^j` and `i_j = lev σ j + 1 ∈ {1, 2}`.
The level-0 term `δ^0_{i_0} = 0` is omitted, so `ω^0 = 0` (the common root). -/
noncomputable def scenario {K : ℕ} (δ : ℕ → ℝ) (σ : Fin K → Fin 2) : Fin (K + 1) → ℝ :=
  fun k => ∑ r ∈ Finset.Icc 1 k.val, (2 * (((lev σ r).val : ℝ) + 1) - 3) * δ r

end ScenarioReduction.BinaryTree
