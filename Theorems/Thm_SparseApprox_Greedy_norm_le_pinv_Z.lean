import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem norm_le_pinv_Z {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u)
    (PZ : Matrix ↥(nzSet u ∪ (greedyState A b k r).chosen) (Fin m) ℝ)
    (hPZ : IsMoorePenrose
      (colsMatrix (fun i : ↥(nzSet u ∪ (greedyState A b k r).chosen) => (initState A b).col i))
      PZ) :
    ‖u‖ ≤ 3 / 2 * opNorm2 PZ * ‖(greedyState A b k r).res‖ := by sorry

end SparseApprox.Greedy
