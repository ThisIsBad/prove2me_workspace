import Mathlib
import Definitions.Def_DantzigSimplex_Technique_Process

namespace DantzigSimplex.Technique

/-- Theorem 1, pp. 341--342, with the two cases of (16) made explicit. -/
theorem theorem_1_improvement {m n : ℕ} (p : Problem m n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : p.Nondegenerate)
    (s : PhaseIIState p) (j : Fin n) (hj : p.cost j > s.frame.z j) :
    (∀ θ : ℝ, 0 < θ → p.Feasible (phaseIIWeights s j θ) →
      p.objective s.weight < p.objective (phaseIIWeights s j θ)) ∧
    (((∃ i ∈ s.frame.B, 0 < s.frame.x i j) ∧
       ∃ (i₀ : Fin n) (θ : ℝ) (t : PhaseIIState p),
         i₀ ∈ s.frame.B ∧ 0 < s.frame.x i₀ j ∧
         θ = s.weight i₀ / s.frame.x i₀ j ∧
         (∀ i ∈ s.frame.B, 0 < s.frame.x i j →
           θ ≤ s.weight i / s.frame.x i j) ∧
         t.frame.B = insert j (s.frame.B.erase i₀) ∧
         t.weight = phaseIIWeights s j θ ∧
         p.objective s.weight < p.objective t.weight) ∨
    ((∀ i ∈ s.frame.B, s.frame.x i j ≤ 0) ∧
       ∀ M : ℝ, ∃ θ : ℝ, 0 < θ ∧
         p.Feasible (phaseIIWeights s j θ) ∧
         M < p.objective (phaseIIWeights s j θ) ∧
         (Finset.univ.filter (fun k => 0 < phaseIIWeights s j θ k)).card = m + 1)) := by sorry

end DantzigSimplex.Technique

