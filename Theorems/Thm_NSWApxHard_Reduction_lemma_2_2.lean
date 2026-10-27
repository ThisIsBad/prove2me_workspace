import Mathlib
import Definitions.Def_NSWApxHard_Reduction_Instance

namespace NSWApxHard.Reduction

/-- Lemma 2.2 (Lee, p. 2): if there are fewer vertex items than vertex agents (`k < N`), some
optimal allocation of the reduced instance gives each vertex agent at most one vertex item. -/
theorem lemma_2_2 {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ) (α : ℝ)
    (hG : IsCubic G) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2) (hk : k < N) :
    ∃ x : Item G k → Agent G,
      IsOptimal (redUtil G k α) x ∧ ∀ v : Fin N, vItems x v ≤ 1 := by sorry

end NSWApxHard.Reduction

