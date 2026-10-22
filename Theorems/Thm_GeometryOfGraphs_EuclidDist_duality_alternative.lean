import Mathlib
import Definitions.Def_GeometryOfGraphs_EuclidDist_EuclideanDistortion

namespace GeometryOfGraphs.EuclidDist

/-- Proof of Corollary 3.5, duality step (pp. 224–225): no positive semidefinite `A` satisfies the
inequalities `J_ij : c^2 d_ij^2 ≥ a_ii + a_jj - 2 a_ij ≥ d_ij^2` iff there are a positive
semidefinite `Q` and nonnegative multipliers `lam, mu` such that adding
`∑ a_ij q_ij ≥ 0` to the combination `∑ lam_ij (upper J_ij) + mu_ij (lower J_ij)` cancels every
`a`-term and leaves a negative constant on the right, i.e. a contradiction. -/
theorem duality_alternative {X : Type*} [Fintype X] [DecidableEq X]
    (d : X → X → ℝ) (hd : GeometryOfGraphs.FlowCut.IsPseudometric d) (c : ℝ) (hc : 1 ≤ c) :
    (¬ ∃ A : Matrix X X ℝ, A.PosSemidef ∧
        ∀ i j, d i j ^ 2 ≤ A i i + A j j - 2 * A i j ∧
          A i i + A j j - 2 * A i j ≤ c ^ 2 * d i j ^ 2) ↔
      ∃ Q : Matrix X X ℝ, Q.PosSemidef ∧
        ∃ lam mu : X → X → ℝ, (∀ i j, 0 ≤ lam i j) ∧ (∀ i j, 0 ≤ mu i j) ∧
          (∀ A : Matrix X X ℝ,
            (∑ i, ∑ j, Q i j * A i j) +
              ∑ i, ∑ j, (lam i j * (c ^ 2 * d i j ^ 2 - (A i i + A j j - 2 * A i j)) +
                mu i j * ((A i i + A j j - 2 * A i j) - d i j ^ 2)) =
            ∑ i, ∑ j, (lam i j * (c ^ 2 * d i j ^ 2) - mu i j * d i j ^ 2)) ∧
          ∑ i, ∑ j, (lam i j * (c ^ 2 * d i j ^ 2) - mu i j * d i j ^ 2) < 0 := by sorry

end GeometryOfGraphs.EuclidDist

