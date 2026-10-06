import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Applications

open MeasureTheory

namespace MDPFinance.OptimalStopping

/-- **Theorem 10.3.6** (p. 326), Example 10.3.5. a) `c_{N-k}(s,k) = (b+s) ĉ_{N-k}` for
`k = 0,…,N-1`, the `ĉ` satisfy the recursion `ĉ_1 = 1/(N+a-2)`, `ĉ_{N-k+1} = (1/(k+a-2))
[(k+a-1) ĉ_{N-k} + ((1-ĉ_{N-k})^+)^{k+a-1}]`, and are increasing in `k`; `n^*(N) := max{k ∈
{1,…,N} | ĉ_{N-k+1} ≥ 1}`. b) The `ĉ_k` are decreasing in `N` and `n^*` increasing in `N`.
c) `f^*_{N-k} ≡ 0` for `k = 0,…,n^*-1` (on the reachable states `0 ≤ x ≤ s`). d) `J_N(0,(0,0)) =
b ĉ_N`. -/
theorem theorem_10_3_6 (M : BayesStopping) (N : ℕ) (hN : 1 ≤ N) :
    ((∀ (k : ℕ) (s : ℝ), k ≤ N - 1 → 0 ≤ s →
        M.cfun (N - k) s k = (M.b + s) * M.chat N (N - k)) ∧
      (M.chat N 1 = 1 / ((N : ℝ) + M.a - 2)) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ N - 1 →
        M.chat N (N - k + 1)
          = (1 / ((k : ℝ) + M.a - 2)) *
              (((k : ℝ) + M.a - 1) * M.chat N (N - k)
                + Real.rpow (max (1 - M.chat N (N - k)) 0) ((k : ℝ) + M.a - 1))) ∧
      (∀ j k : ℕ, 1 ≤ j → j ≤ k → k ≤ N → M.chat N j ≤ M.chat N k)) ∧
    ((∀ (k N₁ N₂ : ℕ), 1 ≤ k → k ≤ N₁ → N₁ ≤ N₂ → M.chat N₂ k ≤ M.chat N₁ k) ∧
      (∀ N₁ N₂ : ℕ, N₁ ≤ N₂ → M.nStar N₁ ≤ M.nStar N₂)) ∧
    (∀ (k : ℕ) (x s : ℝ), k + 1 ≤ M.nStar N → 0 ≤ x → x ≤ s →
      x < M.cfun (N - k) s k) ∧
    (M.J N 0 0 0 = M.b * M.chat N N) := by sorry

end MDPFinance.OptimalStopping

