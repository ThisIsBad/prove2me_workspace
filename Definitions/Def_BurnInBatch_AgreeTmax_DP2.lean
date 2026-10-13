import Mathlib

namespace BurnInBatch.AgreeTmax

/-- Processing time `p_j` of the paper's 1-based job `j` (= `p ⟨j - 1, _⟩`); `0` outside
`1 ≤ j ≤ n`, a value the recursion below never reads for prefix lengths `j ≤ n`. -/
def pOf {n : ℕ} (p : Fin n → ℕ) (j : ℕ) : ℕ :=
  if h : 0 < j ∧ j ≤ n then p ⟨j - 1, by omega⟩ else 0

/-- Due date `d_i` of the paper's 1-based job `i`; `0` outside `1 ≤ i ≤ n` (never read). -/
def dOf {n : ℕ} (d : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : 0 < i ∧ i ≤ n then d ⟨i - 1, by omega⟩ else 0

/-- Algorithm DP2 of Lee, Uzsoy & Martin-Vega (1992), §3, p. 770, as printed:
`f(0) = 0` and, for `j ≥ 1`,
`f(j) = min_{max{1, j-B+1} ≤ i ≤ j} f_i(j)` with
`f_i(j) = f(i-1) + p_j` if `f(i-1) + p_j ≤ d_i`, and `∞` otherwise.
Values lie in `ℕ∞`, with `⊤` the paper's `∞` (`⊤ + p = ⊤` and `¬ ⊤ ≤ d`). The clause
`f(j) = ∞ for j < 0` is never reached, since `i ≥ 1`. -/
def dp2 {n : ℕ} (B : ℕ) (p d : Fin n → ℕ) (j : ℕ) : ℕ∞ :=
  if j = 0 then 0
  else
    -- the minimum, over `i = max{1, j-B+1}, …, j`, of `f_i(j)`
    -- (`if x ≤ y then x else y` is `min x y`, written so that it evaluates)
    (List.range' (max 1 (j - B + 1)) (j + 1 - max 1 (j - B + 1))).attach.foldr
      (fun i acc =>
        let fij : ℕ∞ :=
          if dp2 B p d (i.1 - 1) + (pOf p j : ℕ∞) ≤ (dOf d i.1 : ℕ∞) then
            dp2 B p d (i.1 - 1) + (pOf p j : ℕ∞)
          else ⊤
        if fij ≤ acc then fij else acc)
      ⊤
termination_by j
decreasing_by all_goals (have := List.mem_range'_1.mp i.2; omega)

end BurnInBatch.AgreeTmax
