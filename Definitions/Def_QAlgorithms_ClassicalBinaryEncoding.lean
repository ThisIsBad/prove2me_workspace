import Definitions.Def_QAlgorithms_ClassicalStringComputability

namespace QAlgorithms.LocalHamiltonian
open QAlgorithms.Complexity

/-- A natural number in self-delimiting binary: each bit `β` of `Nat.bits` (least significant
first) is written as the pair `1β`, and `00` ends the number. -/
def encBin (m : ℕ) : Str :=
  (Nat.bits m).flatMap (fun β => [true, β]) ++ [false, false]

end QAlgorithms.LocalHamiltonian
