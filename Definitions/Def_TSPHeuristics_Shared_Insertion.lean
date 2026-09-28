import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel

namespace TSPHeuristics.Shared

/-- `T'` is TOUR(T, k) (p. 570): `k` is not on the subtour `T`, and `T'` is obtained by inserting
`k` into `T` at a position that minimizes the length of the resulting subtour. Inserting at
position `pos` with `0 < pos < T.length` replaces the edge between the entries `pos - 1` and `pos`,
and `pos = 0` or `pos = T.length` replaces the closing edge, so the minimization over positions is
the minimization of (3.1) over the edges `(x, y)` of `T`. For a one-node `T = [i]` every position
gives the two-node tour on `i` and `k`. Ties between positions are resolved arbitrarily. -/
def IsInsertion {n : ℕ} (d : Fin n → Fin n → ℝ) (T : List (Fin n)) (k : Fin n)
    (T' : List (Fin n)) : Prop :=
  k ∉ T ∧ ∃ pos ≤ T.length, T' = T.insertIdx pos k ∧
    ∀ pos' ≤ T.length, cycleLength d T' ≤ cycleLength d (T.insertIdx pos' k)

/-- COST(T, k) (p. 571): the length of TOUR(T, k) minus the length of `T`, i.e. the least
increase in length over all insertion positions. Used only for `k ∉ T`. -/
def insCost {n : ℕ} (d : Fin n → Fin n → ℝ) (T : List (Fin n)) (k : Fin n) : ℝ :=
  (Finset.range (T.length + 1)).inf' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
      (fun pos => cycleLength d (T.insertIdx pos k)) - cycleLength d T

/-- An insertion method run (p. 571) on a graph with `n` nodes, with the paper's 1-based subtour
index: `T 1` is the one-node subtour `[a 0]`, and for `1 ≤ i < n` the node `a i` is not in `T i`
and `T (i + 1)` is TOUR(`T i`, `a i`). `T n` is the approximation; the values of `T` and `a`
outside these indices are irrelevant. -/
def IsInsertionRun {n : ℕ} (d : Fin n → Fin n → ℝ) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) :
    Prop :=
  T 1 = [a 0] ∧ ∀ i, 1 ≤ i → i < n → IsInsertion d (T i) (a i) (T (i + 1))

/-- The distance d(T, p) between a subtour and a node, (4.1): `min {d(x, p) : x ∈ T}`, computed in
`WithTop ℝ` so that no junk value arises (it is `⊤` only for the empty list, which is never a
subtour). -/
def distToTour {n : ℕ} (d : Fin n → Fin n → ℝ) (T : List (Fin n)) (p : Fin n) : WithTop ℝ :=
  T.toFinset.inf (fun x => ((d x p : ℝ) : WithTop ℝ))

/-- Nearest insertion, (4.2): for `1 ≤ i < n`, `d(T_i, a_i) ≤ d(T_i, x)` for every `x ∉ T_i`. -/
def IsNearestRule {n : ℕ} (d : Fin n → Fin n → ℝ) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) :
    Prop :=
  ∀ i, 1 ≤ i → i < n → ∀ x, x ∉ T i → distToTour d (T i) (a i) ≤ distToTour d (T i) x

/-- Cheapest insertion, (4.3): for `1 ≤ i < n`, `COST(T_i, a_i) ≤ COST(T_i, x)` for every
`x ∉ T_i`. -/
def IsCheapestRule {n : ℕ} (d : Fin n → Fin n → ℝ) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) :
    Prop :=
  ∀ i, 1 ≤ i → i < n → ∀ x, x ∉ T i → insCost d (T i) (a i) ≤ insCost d (T i) x

end TSPHeuristics.Shared
