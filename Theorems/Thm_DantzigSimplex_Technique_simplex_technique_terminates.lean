import Mathlib
import Definitions.Def_DantzigSimplex_Technique_Process

namespace DantzigSimplex.Technique

/-- Sections 1--2: the complete Phase I/II procedure, (44)--(45) then (17)--(18). -/
theorem simplex_technique_terminates {m n : ℕ} (p : Problem m n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : p.Nondegenerate)
    (G : Fin m → ℝ) (hgp : GeneralPosition p G)
    (initial : PhaseIState p G) :
    (¬ ∃ f : ℕ → SimplexState p G,
      ∀ k, SimplexStep (f k) (f (k + 1))) ∧
    (∀ s : SimplexState p G, Terminal s →
      (∃ u : PhaseIState p G, s = Sum.inl u ∧
        (∀ j, u.frame.y0 j ≤ 0) ∧ (∀ w, ¬ p.Feasible w)) ∨
      (∃ u : PhaseIIState p, s = Sum.inr u ∧
        ∃ j : Fin n, p.cost j > u.frame.z j ∧
          (∀ i ∈ u.frame.B, u.frame.x i j ≤ 0) ∧ p.Unbounded) ∨
      (∃ u : PhaseIIState p, s = Sum.inr u ∧
        (∀ j, p.cost j ≤ u.frame.z j) ∧ p.MaximumFeasible u.weight)) := by sorry

end DantzigSimplex.Technique

