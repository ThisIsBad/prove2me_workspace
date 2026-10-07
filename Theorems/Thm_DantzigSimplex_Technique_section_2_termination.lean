import Mathlib
import Definitions.Def_DantzigSimplex_Technique_Process

namespace DantzigSimplex.Technique

/-- Section 2, pp. 346--347: Phase I has no infinite pivot run and terminates in (44) or (45). -/
theorem section_2_termination {m n : ℕ} (p : Problem m n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : p.Nondegenerate)
    (G : Fin m → ℝ) (hgp : GeneralPosition p G)
    (initial : PhaseIState p G) :
    (¬ ∃ f : ℕ → PhaseIState p G, ∀ k, PhaseIStep (f k) (f (k + 1))) ∧
    (∀ s : PhaseIState p G,
      (¬ ∃ t : PhaseIState p G, PhaseIStep s t) →
      ((∀ j, s.frame.y0 j ≤ 0) ∧ (∀ w, ¬ p.Feasible w)) ∨
      (∃ j : Fin n, 0 < s.frame.y0 j ∧
        (∀ i ∈ s.frame.S, s.frame.y i j ≤ 0) ∧
        ∃ t : PhaseIIState p, HandOff s t)) := by sorry

end DantzigSimplex.Technique

