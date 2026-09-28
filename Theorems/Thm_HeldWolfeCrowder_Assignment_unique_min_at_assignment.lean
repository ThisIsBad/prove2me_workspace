import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting

namespace HeldWolfeCrowder.Assignment

/-- Held–Wolfe–Crowder (1974), p. 70, Eq. (3.5): if `σ` is the unique optimal one-to-one
assignment, there is an optimal `π̄` for (3.3) such that, for each job `r`, the minimum
`min_s [a_{sr} − π̄_s]` is attained only at the man `s = σ(r)`. -/
theorem unique_min_at_assignment {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) (hσ : IsOptimalAssignment a σ)
    (huniq : ∀ τ : Equiv.Perm (Fin n), IsOptimalAssignment a τ → τ = σ) :
    ∃ πbar : Fin n → ℝ, πbar ∈ optSet a ∧
      ∀ r s : Fin n, s ≠ σ r → a (σ r) r - πbar (σ r) < a s r - πbar s := by sorry

end HeldWolfeCrowder.Assignment

