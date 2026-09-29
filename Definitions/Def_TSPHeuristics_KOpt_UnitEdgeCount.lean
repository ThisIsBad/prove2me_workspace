import Mathlib

namespace TSPHeuristics.KOpt

/-- The unit edges `E_n` of the circle graph (p. 580): "E_n = {(1, n)} ∪ {(i, i + 1) for 1 ≦ i < n}".
With 0-based nodes the unit edge with index `e : Fin n` joins `e` and `e + 1 (mod n)`: index
`e = i - 1` is the paper's `(i, i + 1)` for `1 ≤ i < n`, and index `n - 1` is the paper's `(1, n)`.

`arcCovers n x y e` says that the unit edge `e` lies on the canonical path in `E_n` that replaces the
tour edge `(x, y)`: the shorter of the two arcs of the circle between `x` and `y`, and when the two
arcs have equal length (`n` even, `x`, `y` antipodal) the arc through the nodes
`min x y, min x y + 1, …, max x y`. The arc has `d_n(x, y)` unit edges. The paper replaces "each
edge of T by a path of equal length from E_n" without fixing the path in the tied case; this fixes
one choice so that COUNT is a function. -/
def arcCovers (n : ℕ) (x y e : Fin n) : Prop :=
  if 2 * (max x.val y.val - min x.val y.val) ≤ n then
    min x.val y.val ≤ e.val ∧ e.val < max x.val y.val
  else
    e.val < min x.val y.val ∨ max x.val y.val ≤ e.val

instance (n : ℕ) (x y e : Fin n) : Decidable (arcCovers n x y e) := by
  unfold arcCovers; infer_instance

/-- COUNT(e, T) (p. 580): the number of times the unit edge `e` occurs in the circuit α(τ) obtained
by replacing each edge `(τ k, τ (k + 1))` of the tour `τ` by its canonical arc (`arcCovers`). -/
def unitCount {n : ℕ} (τ : Equiv.Perm (Fin n)) (e : Fin n) : ℕ :=
  (Finset.univ.filter (fun k : Fin n => arcCovers n (τ k) (τ (finRotate n k)) e)).card

end TSPHeuristics.KOpt
