import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_IsEpsNet
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm

namespace HighDimProb.RandomMatrices

/-- **Exercise 4.4.3(a)** (Quadratic form on a net), Vershynin, *High-Dimensional Probability*
(2018), p. 90.

Let `A` be an `m × n` matrix and `ε ∈ [0, 1/2)`. Then for any `ε`-net `N` of the sphere
`Sⁿ⁻¹` and any `ε`-net `M` of the sphere `Sᵐ⁻¹`,
`sup_{x ∈ N, y ∈ M} ⟨Ax, y⟩ ≤ ‖A‖ ≤ (1/(1-2ε)) sup_{x ∈ N, y ∈ M} ⟨Ax, y⟩`. -/
theorem quadratic_form_on_net {m n : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin m) (Fin n) ℝ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (N : Set (EuclideanSpace ℝ (Fin n)))
    (hN : IsEpsNet (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) N ε)
    (M : Set (EuclideanSpace ℝ (Fin m)))
    (hM : IsEpsNet (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) M ε) :
    sSup (Set.image2 (fun x y => inner ℝ (Matrix.toEuclideanLin A x) y) N M)
        ≤ matrixOpNorm A ∧
    matrixOpNorm A ≤ (1 / (1 - 2 * ε)) *
        sSup (Set.image2 (fun x y => inner ℝ (Matrix.toEuclideanLin A x) y) N M) := by sorry

end HighDimProb.RandomMatrices
