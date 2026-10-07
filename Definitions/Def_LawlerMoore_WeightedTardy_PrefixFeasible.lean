import Mathlib

namespace LawlerMoore.WeightedTardy

/-- The constraints of the prefix-constrained knapsack problem of §6 (Lawler–Moore 1969, p. 80):
the 0–1 vector `x` (`x j = true` means `x_j = 1`, job `j` on time; `x j = false` means
`x_j = 0`, job `j` tardy) satisfies
`a'_1 x_1 + ⋯ + a'_k x_k ≤ d_k` for every `k = 1, …, n`.
Lean job `i` is the paper's job `i + 1`, so the `k`-th constraint sums over `i ≤ k`. -/
def PrefixFeasible {n : ℕ} (a' d : Fin n → ℕ) (x : Fin n → Bool) : Prop :=
  ∀ k : Fin n, ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), a' i * (x i).toNat ≤ d k

/-- The objective `∑_{j=1}^n p_j x_j` of the knapsack problems of §6 (p. 80). -/
noncomputable def knapValue {n : ℕ} (p : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ j, p j * ((x j).toNat : ℝ)

end LawlerMoore.WeightedTardy
