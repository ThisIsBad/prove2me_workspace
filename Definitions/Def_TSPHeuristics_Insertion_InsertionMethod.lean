import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel

namespace TSPHeuristics.Insertion

/-- `T'` is a possible `TOUR(T, k)` (p. 570): `k` is not in the subtour `T`, and `T'` is obtained
by inserting `k` into `T` at a position that minimizes the length of the resulting tour. For a
subtour with at least two nodes, inserting at position `pos` deletes the edge between the entries
at `pos - 1` and `pos` (cyclically; positions `0` and `T.length` both delete the closing edge), so
the length grows by exactly `d(x, k) + d(k, y) - d(x, y)` of (3.1), and minimizing the length
minimizes (3.1). For a one-node subtour every position gives the two-node tour. Every minimizing
position (every tie-breaking) is allowed. -/
def IsInsertion {n : ℕ} (d : Fin n → Fin n → ℝ) (T : List (Fin n)) (k : Fin n)
    (T' : List (Fin n)) : Prop :=
  k ∉ T ∧ ∃ pos, pos ≤ T.length ∧ T' = T.insertIdx pos k ∧
    ∀ pos', pos' ≤ T.length → TSPHeuristics.Shared.cycleLength d T' ≤ TSPHeuristics.Shared.cycleLength d (T.insertIdx pos' k)

/-- `COST(T, k)` (p. 571): the length of `TOUR(T, k)` minus the length of `T`, i.e. the least
increase in length over all insertion positions. -/
def insCost {n : ℕ} (d : Fin n → Fin n → ℝ) (T : List (Fin n)) (k : Fin n) : ℝ :=
  (Finset.range (T.length + 1)).inf' ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
    (fun pos => TSPHeuristics.Shared.cycleLength d (T.insertIdx pos k) - TSPHeuristics.Shared.cycleLength d T)

/-- An insertion method run (p. 571), with the paper's 1-based subtour index: `T 1` is the
one-node subtour `[a 0]`, and for every `1 ≤ i < n` the node `a i` is not in `T i` and
`T (i + 1)` is a `TOUR(T i, a i)`. The approximation is `T n`. The choice of the nodes `a i` is
arbitrary (no selection rule), as is the choice among minimizing insertion positions. -/
def IsInsertionRun {n : ℕ} (d : Fin n → Fin n → ℝ) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) :
    Prop :=
  T 1 = [a 0] ∧ ∀ i, 1 ≤ i → i < n → IsInsertion d (T i) (a i) (T (i + 1))

end TSPHeuristics.Insertion
