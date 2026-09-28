import Mathlib

open MeasureTheory

namespace HighDimStat.RandomMatrices

/-- The entrywise expectation of a random matrix, `E[Q] := (E[Q_{ij}])_{ij}`, used throughout
Wainwright, *High-Dimensional Statistics* (2019), Section 6.4.2, to define the matrix moment
generating function, matrix variance, and Bernstein condition. -/
noncomputable def matrixExpectation {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (Q : Ω → Matrix (Fin d) (Fin d) ℝ) (Prob : Measure Ω) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∫ ω, Q ω i j ∂Prob

end HighDimStat.RandomMatrices
