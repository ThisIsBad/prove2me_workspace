import Mathlib.Analysis.Matrix.Order

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §9.1.1, Definition 9.1.1 (Trace Norm).

The trace norm (Schatten 1-norm) of an operator `M ∈ L(H, H')` is
`‖M‖₁ ≡ Tr{|M|}`, where `|M| ≡ √(M†M)`.

Operators are finite-dimensional matrices over `ℂ`; `Mᴴ` is the conjugate transpose (`M†`),
and `CFC.sqrt` is Mathlib's positive square root of a positive semidefinite matrix.
-/

open Matrix
open scoped MatrixOrder

namespace WildeQIT

/-- **Definition 9.1.1 (Trace Norm).** `‖M‖₁ = Tr{|M|}` with `|M| = √(M†M)`,
for a (possibly rectangular) matrix `M : Matrix m n ℂ`. The trace of the positive
semidefinite matrix `√(M†M)` is a real number; we take its real part to land in `ℝ`. -/
noncomputable def traceNorm {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) : ℝ :=
  (Matrix.trace (CFC.sqrt (Mᴴ * M))).re

end WildeQIT
