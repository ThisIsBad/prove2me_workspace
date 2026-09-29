import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess

namespace RelaxationMethod.ConvexDomain

/-- Theorem 3, Case 1, p. 402: if the closed bounded convex set `A ⊆ E_n` has dimension `n`
(its affine span is the whole space), then for every starting point `p₀ ∉ A` the reflexion
process (3.1), (3.2) terminates: some `p_N` lies in `A`. -/
theorem theorem3_case1 {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A) (hspan : affineSpan ℝ A = ⊤)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (h0 : p 0 ∉ A) (hrun : IsImageRun A p) :
    ∃ N : ℕ, p N ∈ A := by sorry

end RelaxationMethod.ConvexDomain

