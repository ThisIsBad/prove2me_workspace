import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_matrixExpectation

open MeasureTheory

namespace HighDimStat.RandomMatrices

/-- **var(Q) := E[Q²] - (E[Q])²**, Wainwright, *High-Dimensional Statistics* (2019), p. 169. The
matrix variance of a random matrix `Q`, a positive semidefinite matrix (Exercise 6.6). -/
noncomputable def matrixVariance {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (Q : Ω → Matrix (Fin d) (Fin d) ℝ) (Prob : Measure Ω) : Matrix (Fin d) (Fin d) ℝ :=
  matrixExpectation (fun ω => Q ω ^ 2) Prob - (matrixExpectation Q Prob) ^ 2

end HighDimStat.RandomMatrices
