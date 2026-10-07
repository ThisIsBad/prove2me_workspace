import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson

namespace QueueingFundamentals.Networks

open Finset

/-- Eqs. (4.19)–(4.21), pp.198–199 (Buzen's algorithm): with `f_i(n) = ρ_i^n / a_i(n)` for a closed
network with `c_i ≥ 1` servers at node `i`,
(1) `G(N) = g_k(N)`;
(2) `g_m(n) = ∑_{i=0}^{n} f_m(i) g_{m−1}(n − i)` for `1 ≤ m ≤ k` (node `m` is index `m − 1`);
(3) `g_1(n) = f_1(n)`;
(4) `g_m(0) = 1`. -/
theorem buzen_recursion {k : ℕ} (rho : Fin k → ℝ) (c : Fin k → ℕ) (hc : ∀ i, 1 ≤ c i) :
    (∀ N : ℕ, normConst (buzenFactor rho c) N = gBuzen (buzenFactor rho c) k le_rfl N) ∧
    (∀ (m : ℕ) (hm : m + 1 ≤ k) (n : ℕ),
      gBuzen (buzenFactor rho c) (m + 1) hm n =
        ∑ i ∈ range (n + 1),
          buzenFactor rho c ⟨m, hm⟩ i * gBuzen (buzenFactor rho c) m (Nat.le_of_succ_le hm) (n - i)) ∧
    (∀ (h1 : 1 ≤ k) (n : ℕ), gBuzen (buzenFactor rho c) 1 h1 n = buzenFactor rho c ⟨0, h1⟩ n) ∧
    (∀ (m : ℕ) (hm : m ≤ k), gBuzen (buzenFactor rho c) m hm 0 = 1) := by sorry

end QueueingFundamentals.Networks

