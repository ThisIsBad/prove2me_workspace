import Mathlib
import Definitions.Def_JohnsonApprox_SubsetSum_Problem

namespace JohnsonApprox.SubsetSum

/-- The lower-bound input of the proof of Theorem 1 (Johnson 1974, p. 261):
`T = {a_1, …, a_{k+2}}` (here `Fin (k + 2)`, with `a_1` the index `0`),
`s(a_1) = 1 + ε`, `s(a_i) = 1` otherwise, and `b = k + 1`. -/
def lowerBoundInput (k : ℕ) (ε : ℚ) (hε : 0 < ε) : Input (Fin (k + 2)) where
  T := Finset.univ
  s := fun i => if i = 0 then 1 + ε else 1
  b := (k : ℚ) + 1
  s_pos := by
    intro x _
    split_ifs <;> linarith
  b_pos := by positivity

end JohnsonApprox.SubsetSum
