import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem nnz_initial_eq_opt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (initState A b).col b (ε / 2) u) :
    nnz u = optSparsity A b (ε / 2) := by sorry

end SparseApprox.Greedy
