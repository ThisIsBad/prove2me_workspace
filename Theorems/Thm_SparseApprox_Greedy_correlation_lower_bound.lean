import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem correlation_lower_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u) :
    ∃ j : Fin n, ‖(greedyState A b k r).res‖ ^ 2 ≤
      2 * Real.sqrt (nnz u) * ‖u‖ * |⟪(greedyState A b k r).col j, (greedyState A b k r).res⟫_ℝ| := by sorry

end SparseApprox.Greedy
