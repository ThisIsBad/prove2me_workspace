import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem greedy_iterations_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε)
    (hA : LinearIndependent ℝ (colE A))
    (hfeas : ∃ x : EuclideanSpace ℝ (Fin n), ‖Matrix.toEuclideanLin A x - b‖ ≤ ε / 2)
    (P : Matrix (Fin n) (Fin m) ℝ) (hP : IsMoorePenrose (Abar A) P)
    (k : ℕ → Fin n) (t : ℕ) (hrun : IsGreedyRun A b ε k t) :
    t ≤ ⌈18 * (optSparsity A b (ε / 2) : ℝ) * opNorm2 P ^ 2 * Real.log (‖b‖ / ε)⌉₊ := by sorry

end SparseApprox.Greedy
