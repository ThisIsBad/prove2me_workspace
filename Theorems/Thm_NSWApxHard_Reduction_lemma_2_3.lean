import Mathlib
import Definitions.Def_NSWApxHard_Reduction_Instance

namespace NSWApxHard.Reduction

/-- Lemma 2.3 (Lee, p. 3): for `α ∈ (1/3, 1/2)` and `k < N`, some optimal allocation of the
reduced instance gives each vertex agent at most one vertex item, and every shared item
`i(v, e)` is allocated by the four-step rule `Rule`. -/
theorem lemma_2_3 {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ) (α : ℝ)
    (hG : IsCubic G) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2) (hk : k < N) :
    ∃ x : Item G k → Agent G, IsOptimal (redUtil G k α) x ∧ (∀ v : Fin N, vItems x v ≤ 1) ∧
      ∀ s : Inc G, Rule x s := by sorry

end NSWApxHard.Reduction

