import Mathlib

namespace HighDimStat.RandomMatrices

/-- **Eq. (6.52)** (hard-thresholding operator), Wainwright, *High-Dimensional Statistics*
(2019), p. 180. The scalar hard-thresholding operator `Tλ(u) := u·I[|u|>λ]`, extended entrywise
to a matrix `M`: `Tλ(M)_{ij} := Tλ(M_{ij})`. -/
noncomputable def thresholdMatrix {d : ℕ} (lam : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => if lam < |M i j| then M i j else 0

end HighDimStat.RandomMatrices
