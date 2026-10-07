import Mathlib
import Definitions.Def_LawlerMoore_WeightedTardy_PrefixFeasible
import Definitions.Def_LawlerMoore_WeightedTardy_eq3

namespace LawlerMoore.WeightedTardy

/-- Eq. (3) (§6, p. 80): for `j ≤ n` and every time `t ≥ 0`, `f(j, t)` is finite and equals the
maximum of `∑ p_i x_i` over the 0–1 vectors `x` that use only the first `j` jobs, satisfy the
prefix constraints `a'_1 x_1 + ⋯ + a'_k x_k ≤ d_k` for `k = 1, …, j`, and have
`a'_1 x_1 + ⋯ + a'_j x_j ≤ t`. -/
theorem eq3_value {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ) (j : ℕ) (hj : j ≤ n) (t : ℕ) :
    ∃ V : ℝ, eq3 a' d p j (t : ℤ) = (V : WithBot ℝ) ∧
      IsGreatest
        {v : ℝ | ∃ x : Fin n → Bool,
          (∀ i : Fin n, j ≤ i.val → x i = false) ∧
          (∀ k : Fin n, k.val < j →
            ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), a' i * (x i).toNat ≤ d k) ∧
          ∑ i, a' i * (x i).toNat ≤ t ∧
          v = knapValue p x}
        V := by sorry

end LawlerMoore.WeightedTardy

