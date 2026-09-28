import Mathlib
import Definitions.Def_LogRegretOCO_ONS_Basic

namespace LogRegretOCO.ONS

/-- Lemma 8 (folklore; Hazan–Agarwal–Kale 2007, p. 188). Let `P ⊆ ℝⁿ` be convex, `A` positive
semidefinite, `y ∈ ℝⁿ`, and `z` a generalized projection of `y` onto `P` with respect to `A`.
Then `(y − a)ᵀ A (y − a) ≥ (z − a)ᵀ A (z − a)` for every `a ∈ P`. -/
theorem gen_proj_ineq {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (hP : Convex ℝ P)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (y z : EuclideanSpace ℝ (Fin n)) (hz : IsGenProj P A y z) :
    ∀ a ∈ P, quadForm A (z - a) ≤ quadForm A (y - a) := by sorry

end LogRegretOCO.ONS

