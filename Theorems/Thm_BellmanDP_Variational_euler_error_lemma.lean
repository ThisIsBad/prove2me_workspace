import Mathlib
import Definitions.Def_BellmanDP_Variational_Approximation

namespace BellmanDP.Variational

open Set

/-- Bellman, *Dynamic Programming*, Ch. IX, § 12, Lemma, p. 261 (corrected: the print's range
`0 ≤ t ≤ N` is the horizon `0 ≤ t ≤ T`, `N = ⌊T n⌋`; the bounds `m ≤ x ≤ M` are imposed on the
solution `x (t)` as well as on the sequence `x_k`, as in the proof of Theorem 2).
Let `G (x, φ)` be Lipschitz for `m ≤ x ≤ M`, `0 ≤ φ ≤ 1`. There is a constant `κ` depending only
on `G`, `T` (and `m`, `M`) such that for every `n ≥ 1`, every step control with values
`0 ≤ φ_k ≤ 1` on `k/n ≤ t < (k+1)/n`, `k = 0, …, N`, whose Euler states `x_k` (12.6) satisfy
`m ≤ x_k ≤ M`, and every solution `x (t)` of `dx/dt = G (x, φ(t))`, `x (0) = x_0`, staying in
`[m, M]`, we have `|x (t) − x̄ (t)| ≤ κ / n` for `0 ≤ t ≤ T`, where `x̄ (t) = x_k` on
`k/n ≤ t < (k+1)/n`. -/
theorem euler_error_lemma (G : ℝ → ℝ → ℝ) (m M T : ℝ) (K : NNReal) (hT : 0 ≤ T)
    (hG : LipschitzOnWith K (fun z : ℝ × ℝ => G z.1 z.2) (Icc m M ×ˢ Icc (0 : ℝ) 1)) :
    ∃ κ : ℝ, ∀ n : ℕ, 0 < n → ∀ (c : ℝ) (φs : ℕ → ℝ) (x : ℝ → ℝ),
      (∀ k ≤ horizonSteps T n, φs k ∈ Icc (0 : ℝ) 1) →
      (∀ k ≤ horizonSteps T n, eulerTraj G c n φs k ∈ Icc m M) →
      IsTrajectory G c (stepControl n φs) T x →
      (∀ t ∈ Icc 0 T, x t ∈ Icc m M) →
      ∀ t ∈ Icc 0 T, |x t - eulerTraj G c n φs ⌊t * n⌋₊| ≤ κ / n := by sorry

end BellmanDP.Variational

