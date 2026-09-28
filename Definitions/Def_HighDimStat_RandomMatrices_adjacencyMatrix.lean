import Mathlib

namespace HighDimStat.RandomMatrices

/-- The **adjacency matrix** `A` of the sparsity graph of `Σ`, Wainwright, *High-Dimensional
Statistics* (2019), p. 181: `A_{jℓ} := I[Σ_{jℓ} ≠ 0]`. -/
noncomputable def adjacencyMatrix {d : ℕ} (Sig : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun j l => if Sig j l ≠ 0 then 1 else 0

end HighDimStat.RandomMatrices
