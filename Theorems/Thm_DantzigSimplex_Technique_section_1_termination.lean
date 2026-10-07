import Mathlib
import Definitions.Def_DantzigSimplex_Technique_Process

namespace DantzigSimplex.Technique

/-- Section 1, pp. 342--343: no basis can recur and terminal states satisfy (17) or (18). -/
theorem section_1_termination {m n : ℕ} (p : Problem m n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : p.Nondegenerate) :
    (¬ ∃ f : ℕ → PhaseIIState p, ∀ k, PhaseIIStep (f k) (f (k + 1))) ∧
    (∀ s : PhaseIIState p,
      (¬ ∃ t : PhaseIIState p, PhaseIIStep s t) →
      (∃ j : Fin n, p.cost j > s.frame.z j ∧
        (∀ i ∈ s.frame.B, s.frame.x i j ≤ 0)) ∨
      (∀ j, p.cost j ≤ s.frame.z j)) := by sorry

end DantzigSimplex.Technique

