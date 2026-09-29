import Mathlib

namespace LovaszSchrijver.OddHole

/-- Deletion of the node `v` (p. 177): the coefficient vector `a` with `a_v` set to `0`.
The right-hand side `b` is unchanged. -/
def deletion {V : Type} [DecidableEq V] (a : V → ℝ) (v : V) : V → ℝ :=
  Function.update a v 0

/-- Contraction of the node `v` (p. 177): the coefficient vector `a` with the coefficients
of `v` and of every neighbour of `v` set to `0`. The right-hand side becomes `b - a_v`. -/
def contraction {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V → ℝ) (v : V) : V → ℝ :=
  fun w => if w = v ∨ G.Adj v w then 0 else a w

end LovaszSchrijver.OddHole
