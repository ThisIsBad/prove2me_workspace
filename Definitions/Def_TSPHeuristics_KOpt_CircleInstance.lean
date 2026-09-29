import Mathlib

namespace TSPHeuristics.KOpt

/-- The distance of the graph `(N_n, d_n)` in the proof of Theorem 5 (p. 575): "d_n(i, j) =
smallest nonnegative integer m such that i − j ≡ m (mod n) or j − i ≡ m (mod n)", i.e. the
distance between `i` and `j` along a cycle of `n` equally spaced nodes. The paper's node `m`
(`1 ≤ m ≤ n`) is `⟨m - 1, _⟩ : Fin n`; the shift does not change any difference mod `n`. -/
def cycDist (n : ℕ) (i j : Fin n) : ℝ :=
  ((min ((i.val + n - j.val) % n) ((j.val + n - i.val) % n) : ℕ) : ℝ)

/-- The subtours `T_i` of the proof of Theorem 5 (p. 576), with the paper's 1-based index `i`:
"T_1 [is] the tour on set {1}, … T_2 = {(1, 2), (2, 1)} and for 3 ≦ i ≦ n …
T_i = {(1, 2), (i − 1, i)} ∪ {(j, j + 2) | 1 ≦ j ≦ i − 2}."
As a closed list (0-based nodes, paper node `m` is `m - 1`), `T_i` visits the paper's node 1, then
the even nodes `2, 4, …` up to `i` in increasing order, then the odd nodes in `(1, i]` in decreasing
order, and returns to 1: `T_8 = 1, 2, 4, 6, 8, 7, 5, 3` (Fig. 4), `T_7 = 1, 2, 4, 6, 7, 5, 3`,
`T_3 = 1, 2, 3`, `T_2 = 1, 2`, `T_1 = 1`. Its edges are exactly the paper's edge set. -/
def circleSubtour (n i : ℕ) : List (Fin n) :=
  (List.finRange n).filter (fun m => m.val < i ∧ m.val = 0) ++
    (List.finRange n).filter (fun m => m.val < i ∧ Odd m.val) ++
    ((List.finRange n).filter (fun m => m.val < i ∧ m.val ≠ 0 ∧ Even m.val)).reverse

/-- The inserted nodes of the proof of Theorem 5 (p. 576): "a_i = i + 1 for 0 ≦ i < n". With
0-based nodes the paper's node `i + 1` is `⟨i, _⟩`, so `circleNode n hn i = ⟨i, _⟩` for `i < n`
(the reduction mod `n` only makes the function total). -/
def circleNode (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin n :=
  ⟨i % n, Nat.mod_lt i hn⟩

end TSPHeuristics.KOpt
