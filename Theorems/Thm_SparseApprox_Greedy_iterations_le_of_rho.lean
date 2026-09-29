import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem iterations_le_of_rho {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (u : ℕ → EuclideanSpace ℝ (Fin n))
    (hu : ∀ r < t,
      IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) (u r))
    (ρ : ℝ)
    (hρ : ∀ r < t, 4 * (nnz (u r) : ℝ) * ‖u r‖ ^ 2 ≤ ρ * ‖(greedyState A b k r).res‖ ^ 2) :
    t ≤ ⌈2 * ρ * Real.log (‖b‖ / ε)⌉₊ := by sorry

end SparseApprox.Greedy
