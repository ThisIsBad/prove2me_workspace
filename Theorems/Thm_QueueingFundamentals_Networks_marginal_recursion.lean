import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson

namespace QueueingFundamentals.Networks

/-- Eq. (4.26), p.204 (proved pp.207–209): for a closed Jackson network of `k ≥ 1` single-server
nodes (rates `μ_i > 0`, irreducible routing `R`) and its steady-state distributions `p_N`
(`N = 0, 1, 2, …`), the marginal probabilities `p_i(n, N)` satisfy `p_i(0, 0) = 1` and
`p_i(n, N) = (λ_i(N)/μ_i) p_i(n − 1, N − 1)` for `n, N ≥ 1`, where
`λ_i(N) = Pr{server busy at node i} · μ_i` is the throughput of node `i`. -/
theorem marginal_recursion {k : ℕ} [NeZero k] (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ)
    (hmu : ∀ i, 0 < mu i) (hR : IsRoutingMatrix R) (hirr : IsIrreducible R)
    (p : ℕ → (Fin k → ℕ) → ℝ) (hp : ∀ N, IsClosedSteadyState mu R N (p N)) (i : Fin k) :
    marginal 0 (p 0) i 0 = 1 ∧
      ∀ n N : ℕ, 1 ≤ n → 1 ≤ N →
        marginal N (p N) i n =
          throughput mu N (p N) i / mu i * marginal (N - 1) (p (N - 1)) i (n - 1) := by sorry

end QueueingFundamentals.Networks

