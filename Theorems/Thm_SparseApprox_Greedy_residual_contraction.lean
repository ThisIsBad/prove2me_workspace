import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem residual_contraction {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u)
    (ρ : ℝ) (hρ : 4 * (nnz u : ℝ) * ‖u‖ ^ 2 ≤ ρ * ‖(greedyState A b k r).res‖ ^ 2) :
    ρ * ‖(greedyState A b k (r + 1)).res‖ ^ 2 ≤ (ρ - 1) * ‖(greedyState A b k r).res‖ ^ 2 := by sorry

end SparseApprox.Greedy
