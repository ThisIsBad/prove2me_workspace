import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem sparsity_nonincreasing {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t)
    (u₀ u u' : EuclideanSpace ℝ (Fin n))
    (hu₀ : IsMinSparseSol (greedyState A b k 0).col (greedyState A b k 0).res (ε / 2) u₀)
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u)
    (hu' : IsMinSparseSol (greedyState A b k (r + 1)).col (greedyState A b k (r + 1)).res
      (ε / 2) u') :
    nnz u' ≤ nnz u ∧ nnz u ≤ nnz u₀ := by sorry

end SparseApprox.Greedy
