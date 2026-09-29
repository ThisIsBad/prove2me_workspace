import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem opNorm2_pinv_submatrix_le {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : LinearIndependent ℝ (colE M))
    (P : Matrix (Fin n) (Fin m) ℝ) (hP : IsMoorePenrose M P)
    (S : Finset (Fin n)) (PS : Matrix ↥S (Fin m) ℝ)
    (hPS : IsMoorePenrose (colsMatrix (fun i : ↥S => colE M i)) PS) :
    opNorm2 PS ≤ opNorm2 P := by sorry

end SparseApprox.Greedy
