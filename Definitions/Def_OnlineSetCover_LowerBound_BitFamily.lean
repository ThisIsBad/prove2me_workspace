import Mathlib

namespace OnlineSetCover.LowerBound

/-- The set `F_{t+1}` of Proposition 4.1 (Alon et al. 2009, p. 368): the elements `j` of
`X = {0, 1, …, 2^k − 1}` whose bit number `t + 1` (counting from the least significant bit,
which is bit `1`) is on, i.e. `Nat.testBit j t`. -/
def bitSet (k : ℕ) (t : Fin k) : Finset (Fin (2 ^ k)) :=
  Finset.univ.filter (fun j => j.val.testBit t.val)

/-- The family `F = {F_1, …, F_k}` of Proposition 4.1 on `X = {0, …, 2^k − 1}`. -/
def bitFamily (k : ℕ) : Finset (Finset (Fin (2 ^ k))) :=
  Finset.univ.image (bitSet k)

end OnlineSetCover.LowerBound
