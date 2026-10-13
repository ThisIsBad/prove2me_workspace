import Mathlib
import Definitions.Def_BurnInBatch_ReleaseTmax_Model

namespace BurnInBatch.ReleaseTmax

/-- A job datum extended to all natural-number indices: the value of the 0-based job `k` for
`k < n`, and `0` beyond (those values are never used for prefix lengths `j ≤ n`). -/
def jobVal {n : ℕ} (f : Fin n → ℕ) (k : ℕ) : ℕ :=
  if h : k < n then f ⟨k, h⟩ else 0

/-- Algorithm DP1 (p. 768). `dp1 B p r d j` is the paper's `f(j)` for the prefix of length `j`:
`f(0) = 0` and, for `j ≥ 1`,
`f(j) = min_{max{1, j − B + 1} ≤ i ≤ j} f_i(j)` with
`f_i(j) = max{f(i − 1), r_j} + p` if `max{f(i − 1), r_j} + p ≤ d_i`, and `∞` otherwise.
Indices `i, j` are 1-based as in the paper: `r_j = jobVal r (j - 1)`, `d_i = jobVal d (i - 1)`.
The value `∞` is `⊤ : ℕ∞`, and a minimum over an empty range would be `⊤`. -/
noncomputable def dp1 {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ) : ℕ → ℕ∞
  | 0 => 0
  | j + 1 =>
      (Finset.Icc (max 1 (j + 1 + 1 - B)) (j + 1)).attach.inf fun i =>
        have : i.val - 1 < j + 1 := by
          have := (Finset.mem_Icc.mp i.property).2
          omega
        let s : ℕ∞ := max (dp1 B p r d (i.val - 1)) (jobVal r j : ℕ∞) + p
        if s ≤ (jobVal d (i.val - 1) : ℕ∞) then s else ⊤
termination_by j => j

end BurnInBatch.ReleaseTmax
