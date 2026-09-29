import Mathlib

namespace NagamochiIbaraki.EdgeConn

/-! Procedure FOREST (Nagamochi–Ibaraki 1992, pp. 584–585, lines 1–11), as a nondeterministic
transition system. Line 5 ("an unscanned node with the largest r") and line 6 ("for each
unscanned edge incident to x") leave choices open; every choice is a legal step. -/

variable {V E : Type*}

/-- A state of FOREST.
* `r v` is the label `r(v)`;
* `idx e` is the class of the edge `e`: `0` while `e` is unscanned, and `i ≥ 1` once `e ∈ E_i`;
* `done` is the set of nodes marked "scanned" (line 11);
* `cur = some x` while the for-loop of line 6 runs for the node `x` chosen at line 5;
* `order` lists the nodes in the order line 5 chose them. -/
structure State (V E : Type*) where
  r : V → ℕ
  idx : E → ℕ
  done : Finset V
  cur : Option V
  order : List V

/-- The initial state (lines 1–3): all classes empty, every node and edge unscanned, `r ≡ 0`. -/
def init : State V E where
  r := fun _ => 0
  idx := fun _ => 0
  done := ∅
  cur := none
  order := []

/-- One step of FOREST.
* **select** (line 5): no node is being processed, and `x` is an unscanned node whose label is
  largest among the unscanned nodes; `x` becomes the current node.
* **scan** (lines 6–10): `e` is an unscanned edge joining the current node `x` to `y`. Line 7
  puts `e` into `E_{r(y)+1}`; line 8 increments `r(x)` if `r(x) = r(y)`; line 9 increments
  `r(y)`; line 10 marks `e` scanned (its class becomes nonzero). Lines 7 and 8 use the value of
  `r(y)` before line 9.
* **finish** (line 11): the current node `x` has no unscanned incident edge left; `x` is marked
  scanned. -/
def Step [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V) (s t : State V E) : Prop :=
  (∃ x : V, s.cur = none ∧ x ∉ s.done ∧ (∀ v, v ∉ s.done → s.r v ≤ s.r x) ∧
      t = { s with cur := some x, order := s.order ++ [x] }) ∨
  (∃ (x y : V) (e : E), s.cur = some x ∧ s.idx e = 0 ∧ ends e = s(x, y) ∧
      t = { s with
              idx := Function.update s.idx e (s.r y + 1),
              r := Function.update
                (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
                y (s.r y + 1) }) ∨
  (∃ x : V, s.cur = some x ∧ (∀ e : E, x ∈ ends e → s.idx e ≠ 0) ∧
      t = { s with done := insert x s.done, cur := none })

/-- `σ 0, σ 1, …, σ K` is an execution of FOREST of length `K` from the initial state. -/
def IsRun [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V) (σ : ℕ → State V E) (K : ℕ) :
    Prop :=
  σ 0 = init ∧ ∀ k, k < K → Step ends (σ k) (σ (k + 1))

/-- A completed execution: at time `K` every node is scanned, so the while-test of line 4 fails
and FOREST terminates. -/
def IsCompletedRun [Fintype V] [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V)
    (σ : ℕ → State V E) (K : ℕ) : Prop :=
  IsRun ends σ K ∧ (σ K).done = Finset.univ

/-- The class `E_i` held by the state `s` (the set `E_i` "at that time instant"). -/
def cls [Fintype E] (s : State V E) (i : ℕ) : Finset E :=
  Finset.univ.filter (fun e => s.idx e = i)

/-- The edge set `E_1 ∪ E_2 ∪ ⋯ ∪ E_i` of `G_i` held by the state `s`
(empty for `i = 0`). -/
def upto [Fintype E] (s : State V E) (i : ℕ) : Finset E :=
  Finset.univ.filter (fun e => 1 ≤ s.idx e ∧ s.idx e ≤ i)

end NagamochiIbaraki.EdgeConn
