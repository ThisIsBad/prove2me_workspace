import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- Munkres (1957), §1, pp. 33–35: correctness of the assignment algorithm on every real
`n × n` matrix `A`. The Preliminaries can be carried out; every run is finite; no run gets stuck
before it stops; and when it stops, the starred zeros are the positions `(σ r, r)` of a
permutation `σ` that is an optimal assignment for the original matrix `A`. -/
theorem munkres_algorithm_correct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (∃ s₀, IsStart A s₀) ∧
    (∀ s₀, IsStart A s₀ → Acc (fun t s => Step s t) s₀) ∧
    (∀ s, Reachable A s → s.phase ≠ Phase.done → ∃ t, Step s t) ∧
    (∀ s, Reachable A s → s.phase = Phase.done →
      ∃ σ : Equiv.Perm (Fin n), s.starred = Finset.univ.image (fun r => (σ r, r)) ∧
        HeldWolfeCrowder.Assignment.IsOptimalAssignment A σ) := by sorry

end MunkresAlg.Assignment

