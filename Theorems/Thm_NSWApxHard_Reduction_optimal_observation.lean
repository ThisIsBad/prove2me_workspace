import Mathlib
import Definitions.Def_NSWApxHard_Reduction_Instance

namespace NSWApxHard.Reduction

/-- Observation (Lee, p. 2): in any optimal allocation of the reduced instance, each vertex item
is assigned to some vertex agent, and each edge item `i(e)` to the edge agent `a(e)`. -/
theorem optimal_observation {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ)
    (α : ℝ) (hG : IsCubic G) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2)
    (x : Item G k → Agent G) (hx : IsOptimal (redUtil G k α) x) :
    (∀ j : Fin k, ∃ v : Fin N, x (Sum.inl j) = Sum.inl v) ∧
      ∀ e : Edge G, x (Sum.inr (Sum.inl e)) = Sum.inr e := by sorry

end NSWApxHard.Reduction

