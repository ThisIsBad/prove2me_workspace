import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson

namespace QueueingFundamentals.Networks

open Finset

/-- Eqs. (4.23)–(4.25) and the MVA algorithm, pp.201–202: for a closed Jackson network of `k ≥ 1`
single-server nodes (rates `μ_i > 0`, irreducible routing `R`) and its steady-state distributions
`p_N` (`N = 0, 1, 2, …`), with `L_i(N)` the mean number at node `i`, `λ_i(N)` the throughput and
`W_i(N) = (1 + L_i(N − 1))/μ_i` (4.23):
(1) `L_i(0) = 0`;
(2) `L_i(N) = λ_i(N) W_i(N)` for `N ≥ 1` (4.24);
(3) for any solution `v` of (4.25) with `v_l = 1`, and `N ≥ 1`:
`λ_l(N) = N / ∑_i v_i W_i(N)` and `λ_i(N) = λ_l(N) v_i`. -/
theorem mean_value_analysis {k : ℕ} [NeZero k] (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ)
    (hmu : ∀ i, 0 < mu i) (hR : IsRoutingMatrix R) (hirr : IsIrreducible R)
    (p : ℕ → (Fin k → ℕ) → ℝ) (hp : ∀ N, IsClosedSteadyState mu R N (p N)) :
    (∀ i, meanNumber 0 (p 0) i = 0) ∧
    (∀ (N : ℕ), 1 ≤ N → ∀ i,
      meanNumber N (p N) i =
        throughput mu N (p N) i * ((1 + meanNumber (N - 1) (p (N - 1)) i) / mu i)) ∧
    (∀ (v : Fin k → ℝ) (l : Fin k), IsVisitRatio R v → v l = 1 →
      ∀ (N : ℕ), 1 ≤ N →
        throughput mu N (p N) l =
            (N : ℝ) / ∑ i, v i * ((1 + meanNumber (N - 1) (p (N - 1)) i) / mu i) ∧
          ∀ i, throughput mu N (p N) i = throughput mu N (p N) l * v i) := by sorry

end QueueingFundamentals.Networks

