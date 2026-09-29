import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
open MasekPaterson.Shared

namespace MasekPaterson.Necessity

/-- A single move of an edit path through the edit matrix, whose entry `(p, q)` stands for
`δ_{p,q} = δ(γ, A^p, B^q)` (`p` indexes `A`, `q` indexes `B`):
* `del` goes from `(p, q)` to `(p + 1, q)` and deletes `A_{p+1}`;
* `ins` goes from `(p, q)` to `(p, q + 1)` and inserts `B_{q+1}`;
* `rep` goes from `(p, q)` to `(p + 1, q + 1)` and replaces `A_{p+1}` by `B_{q+1}`. -/
inductive Move
  | del
  | ins
  | rep
  deriving DecidableEq

/-- The matrix cell reached by a move from the cell `x = (p, q)`. -/
def Move.next : Move → ℕ × ℕ → ℕ × ℕ
  | .del, x => (x.1 + 1, x.2)
  | .ins, x => (x.1, x.2 + 1)
  | .rep, x => (x.1 + 1, x.2 + 1)

variable {α : Type*}

/-- The cost of a move made from the cell `x = (p, q)`, for the cost function `γ` and the
strings `A, B`, given as 1-based sequences of symbols (`A (p + 1)` is `A_{p+1}`):
`D_{A_{p+1}}` for a deletion, `I_{B_{q+1}}` for an insertion, `R_{A_{p+1}, B_{q+1}}` for a
replacement. -/
def Move.cost (γ : EditOp α → ℝ) (A B : ℕ → α) : Move → ℕ × ℕ → ℝ
  | .del, x => delCost γ (A (x.1 + 1))
  | .ins, x => insCost γ (B (x.2 + 1))
  | .rep, x => replCost γ (A (x.1 + 1)) (B (x.2 + 1))

/-- The last cell of the edit path that starts at `x` and makes the moves `ms` in order. -/
def pathEnd : ℕ × ℕ → List Move → ℕ × ℕ
  | x, [] => x
  | x, m :: ms => pathEnd (m.next x) ms

/-- All cells visited by the edit path that starts at `x` and makes the moves `ms`,
the starting cell and the last cell included. -/
def pathPoints : ℕ × ℕ → List Move → List (ℕ × ℕ)
  | x, [] => [x]
  | x, m :: ms => x :: pathPoints (m.next x) ms

/-- The cost of the edit path that starts at `x` and makes the moves `ms`: the sum of the
costs of its operations. -/
def pathCost (γ : EditOp α → ℝ) (A B : ℕ → α) : ℕ × ℕ → List Move → ℝ
  | _, [] => 0
  | x, m :: ms => m.cost γ A B x + pathCost γ A B (m.next x) ms

/-- The minimum cost of an edit path from the cell `x` to the cell `y` (the infimum of the
costs of all move lists from `x` that end at `y`). -/
noncomputable def pathMin (γ : EditOp α → ℝ) (A B : ℕ → α) (x y : ℕ × ℕ) : ℝ :=
  sInf {c : ℝ | ∃ ms : List Move, pathEnd x ms = y ∧ c = pathCost γ A B x ms}

/-- The eccentricity `|i - j|` of the cell `(i, j)`. -/
def ecc (x : ℕ × ℕ) : ℕ := ((x.1 : ℤ) - (x.2 : ℤ)).natAbs

end MasekPaterson.Necessity
