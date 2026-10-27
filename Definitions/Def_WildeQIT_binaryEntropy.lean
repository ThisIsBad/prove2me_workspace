import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Definition 10.1.2 (Binary entropy):
`h₂(p) ≡ -p log p - (1-p) log(1-p)` for `p ∈ [0,1]`, logarithm base 2.
-/

namespace WildeQIT

/-- Definition 10.1.2. The binary entropy function `h₂(p) = -p log₂ p - (1-p) log₂ (1-p)`.
Defined for every real `p` (Wilde: `p ∈ [0,1]`); at `p = 0` and `p = 1` the convention
`0 log 0 = 0` is automatic since `Real.logb 2 0 = 0`. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  -(p * Real.logb 2 p) - (1 - p) * Real.logb 2 (1 - p)

end WildeQIT
