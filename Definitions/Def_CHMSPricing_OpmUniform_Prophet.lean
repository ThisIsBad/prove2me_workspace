import Mathlib

namespace CHMSPricing.OpmUniform

/-- Order statistics (App. D.2, p. 18), 0-based: `orderStat x i` is the `(i+1)`-th largest of
the values `x 0, …, x (n-1)`, counted with multiplicity (`orderStat x 0` is the maximum, i.e.
the paper's `X₍₁₎`). Out of range (`i ≥ n`) it is `0`. -/
noncomputable def orderStat {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  ((Finset.univ.val.map x).sort (fun a b => b ≤ a)).getD i 0

open Classical in
/-- The threshold stopping rule (App. D.2, p. 18), 0-based: for `i : Fin k` (with `k ≤ n`),
`threshIdx hk x c i` is the lesser of the index `n − k + i` and the `(i+1)`-th smallest index
`j` with `x j ≥ c`, or simply `n − k + i` when fewer than `i + 1` indices reach `c`. This is the
paper's `t_{i+1}(c)`. -/
noncomputable def threshIdx {n k : ℕ} (hk : k ≤ n) (x : Fin n → ℝ) (c : ℝ) (i : Fin k) :
    Fin n :=
  let forced : Fin n := ⟨n - k + i, by omega⟩
  match ((Finset.univ.filter (fun j => c ≤ x j)).sort (· ≤ ·))[(i : ℕ)]? with
  | some j => min forced j
  | none => forced

end CHMSPricing.OpmUniform
