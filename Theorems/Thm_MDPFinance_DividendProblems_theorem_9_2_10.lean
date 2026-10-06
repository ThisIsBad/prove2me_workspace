import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend
import Definitions.Def_MDPFinance_DividendProblems_BandPolicy

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace MDPFinance.DividendProblems

/-- Theorem 9.2.10 (Bäuerle–Rieder, p. 279, PDF 289). a) If `\mathbb P(Z \ge -z_0) = 1` for some
`z_0 \in \mathbb N`, then the length of the waves of `f^*` is bounded by `z_0`: `f^*` has a
band-policy parametrization `(n,c,d)` (Definition 9.2.5) with every wave length `d_k - c_{k-1}
\le z_0`. b) If `\mathbb P(Z \ge -1) = 1` then `(f^*,f^*,\dots)` is a barrier-policy. -/
theorem theorem_9_2_10 (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    (∀ z0 : ℕ, 0 < z0 → M.Zpmf.toMeasure {k : ℤ | -(z0 : ℤ) ≤ k} = 1 →
        ∃ n : ℕ, ∃ c d : ℕ → ℕ,
          ((∀ k, 1 ≤ k → k ≤ n → d k - c (k - 1) ≥ 2) ∧ c 0 < d 1 ∧
              (∀ k, 1 ≤ k → k < n → c k < d (k + 1)) ∧ (∀ k, 1 ≤ k → k ≤ n → d k ≤ c k) ∧
              (∀ x, x ≤ c 0 → fstar (x : ℤ) = 0) ∧
              (∀ k, k < n → ∀ x, c k < x → x < d (k + 1) → fstar (x : ℤ) = x - c k) ∧
              (∀ k, 1 ≤ k → k ≤ n → ∀ x, d k ≤ x → x ≤ c k → fstar (x : ℤ) = 0) ∧
              ∀ x, c n < x → fstar (x : ℤ) = x - c n) ∧
            ∀ k, 1 ≤ k → k ≤ n → waveLength c d k ≤ z0) ∧
      (M.Zpmf.toMeasure {k : ℤ | -1 ≤ k} = 1 →
        IsBarrierPolicy (fun x : ℕ => fstar (x : ℤ))) := by sorry

end MDPFinance.DividendProblems

