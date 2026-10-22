import Mathlib
import Definitions.Def_SelfDualLP_Complexity_HLP
import Definitions.Def_SelfDualLP_Complexity_BitLength

open Matrix

namespace SelfDualLP.Complexity

/-- Theorem 6, first sentence (p. 61). For integer data `(A, b, c)` with `n ≥ 1` and bit length `L`, the data
of (HLP) under (7) remain integral — `b̄ = b − Ae`, `c̄ = c − e`, `z̄ = cᵀe + 1` are the casts of
the integer vectors/number `bbarInt`, `cbarInt`, `zbarInt` — and the bit length of the (HLP)
data is `O(L)`: at most `C·L` for an absolute constant `C`. -/
theorem theorem_6_data :
    ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ), 1 ≤ n →
      ∀ (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ),
      bbar (castMat A) (castVec b) (ones n) = castVec (bbarInt A b) ∧
      cbar (castMat A) (castVec c) 0 (ones n) = castVec (cbarInt c) ∧
      zbar (castVec b) (castVec c) (ones n) 0 = ((zbarInt c : ℤ) : ℝ) ∧
      (hlpBitLength A b c : ℝ) ≤ C * (bitLength A b c : ℝ) := by sorry

end SelfDualLP.Complexity

