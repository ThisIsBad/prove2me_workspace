import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson

namespace QueueingFundamentals.Networks

/-- Eq. (4.22), p.199: in a closed network of `k + 1` nodes (the last node is node `k + 1` of the book,
index `Fin.last k`) with `c_i ≥ 1` servers at node `i` and `ρ_i > 0`, under the product form (4.17)
the marginal distribution of the last node is `p_{k+1}(n) = f_{k+1}(n) g_k(N − n) / G(N)` for
`n = 0, 1, …, N`. -/
theorem last_node_marginal {k : ℕ} (rho : Fin (k + 1) → ℝ) (c : Fin (k + 1) → ℕ)
    (hrho : ∀ i, 0 < rho i) (hc : ∀ i, 1 ≤ c i) (N n : ℕ) (hn : n ≤ N) :
    marginal N (productForm (buzenFactor rho c) N) (Fin.last k) n =
      buzenFactor rho c (Fin.last k) n * gBuzen (buzenFactor rho c) k (Nat.le_succ k) (N - n) /
        normConst (buzenFactor rho c) N := by sorry

end QueueingFundamentals.Networks

