import Mathlib
import Definitions.Def_DeterioratingJobs_Makespan_InterchangeSum

namespace DeterioratingJobs.Makespan

/-- Lemma 1 (Browne–Yechiali 1990, p. 495). For `γ_i > 1`, the sum (1)
`∑_i μ_{π(i)} ∏_{r>i} γ_{π(r)}` is minimized over all permutations by any permutation that lists the
jobs by increasing `μ_i / (γ_i - 1)`, and maximized by any that lists them by decreasing values. -/
theorem lemma1_interchange {N : ℕ} (μ γ : Fin N → ℝ) (hγ : ∀ i, 1 < γ i)
    (π : Equiv.Perm (Fin N)) :
    (Monotone (fun k : Fin N => μ (π k) / (γ (π k) - 1)) →
        ∀ σ : Equiv.Perm (Fin N), lemma1Sum μ γ π ≤ lemma1Sum μ γ σ) ∧
      (Antitone (fun k : Fin N => μ (π k) / (γ (π k) - 1)) →
        ∀ σ : Equiv.Perm (Fin N), lemma1Sum μ γ σ ≤ lemma1Sum μ γ π) := by sorry

end DeterioratingJobs.Makespan

