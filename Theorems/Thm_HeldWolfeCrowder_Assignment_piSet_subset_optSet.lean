import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting

namespace HeldWolfeCrowder.Assignment

/-- Held–Wolfe–Crowder (1974), p. 70, Eq. (3.6): for an optimal one-to-one assignment `σ`, on
the set `Π` of (3.6) the minimum in the representation (3.4) is attained only at the assignment
`σ`, whose vector `v_σ` is `0`; `Π` is convex and open, and it is contained in the optimal set
of (3.3). -/
theorem piSet_subset_optSet {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) (hσ : IsOptimalAssignment a σ) :
    (∀ π ∈ PiSet a σ, ∀ A : Fin n → Fin n,
        assignCost a A + ∑ i, π i * assignVec A i ≤ assignCost a σ + ∑ i, π i * assignVec σ i →
          A = σ) ∧
      (∀ i, assignVec σ i = 0) ∧
      Convex ℝ (PiSet a σ) ∧ IsOpen (PiSet a σ) ∧ PiSet a σ ⊆ optSet a := by sorry

end HeldWolfeCrowder.Assignment

