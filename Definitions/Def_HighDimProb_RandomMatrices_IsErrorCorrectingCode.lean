import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_hammingDist

namespace HighDimProb.RandomMatrices

/-- **Definition 4.3.3** (Error correcting code), Vershynin, *High-Dimensional Probability*
(2018), p. 87-88. Fix integers `k, n, r`. Maps `E : {0,1}^k → {0,1}^n` and `D : {0,1}^n →
{0,1}^k` are encoding and decoding maps that can correct `r` errors if `D(y) = x` for every
word `x ∈ {0,1}^k` and every string `y ∈ {0,1}^n` that differs from `E(x)` in at most `r` bits
(Hamming distance `≤ r`). -/
def IsErrorCorrectingCode {k n r : ℕ} (E : (Fin k → Bool) → (Fin n → Bool))
    (D : (Fin n → Bool) → (Fin k → Bool)) : Prop :=
  ∀ x : Fin k → Bool, ∀ y : Fin n → Bool, hammingDist y (E x) ≤ r → D y = x

end HighDimProb.RandomMatrices
