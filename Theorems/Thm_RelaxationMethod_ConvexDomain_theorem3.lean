import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess
import Definitions.Def_RelaxationMethod_ConvexDomain_SymmetricWrt

namespace RelaxationMethod.ConvexDomain

/-- Theorem 3, p. 402. Let `A ⊆ E_n` be a nonempty closed bounded convex set with affine span
`L_r = affineSpan ℝ A`, and let `p₀ ∉ A` start a run of the reflexion process (3.1), (3.2).
Case 1: if `L_r` is the whole space (`r = n`), the process terminates.
Case 2: if `L_r ≠ ⊤` (`r < n`): if `p₀ ∈ L_r` the process terminates; if `p₀ ∉ L_r` the process
never enters `A` and, for all `ν > ν₀`, `p_ν` alternates between two distinct points `u`, `v`
symmetric with respect to `L_r`. -/
theorem theorem3 {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (h0 : p 0 ∉ A) (hrun : IsImageRun A p) :
    (affineSpan ℝ A = ⊤ → ∃ N : ℕ, p N ∈ A) ∧
    (affineSpan ℝ A ≠ ⊤ →
      (p 0 ∈ affineSpan ℝ A → ∃ N : ℕ, p N ∈ A) ∧
      (p 0 ∉ affineSpan ℝ A →
        (∀ ν : ℕ, p ν ∉ A) ∧
        ∃ ν₀ : ℕ, ∃ u v : EuclideanSpace ℝ (Fin n), u ≠ v ∧
          IsSymmetricWrt (affineSpan ℝ A) u v ∧
          ∀ ν : ℕ, ν > ν₀ →
            (p ν = u ∧ p (ν + 1) = v) ∨ (p ν = v ∧ p (ν + 1) = u))) := by sorry

end RelaxationMethod.ConvexDomain

