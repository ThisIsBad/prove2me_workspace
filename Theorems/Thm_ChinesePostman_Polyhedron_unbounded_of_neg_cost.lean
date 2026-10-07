import Mathlib
import Definitions.Def_ChinesePostman_Polyhedron_Setting

namespace ChinesePostman.Polyhedron

theorem unbounded_of_neg_cost {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (c : E → ℝ)
    (e₀ : E) (h : c e₀ < 0) :
    (∀ x ∈ postmanPolyhedron G, ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧
        x + t • Pi.single e₀ 1 ∈ postmanPolyhedron G ∧
        objective c (x + t • Pi.single e₀ 1) < M) ∧
      (∀ x ∈ parityPoints G, ∀ M : ℝ, ∃ k : ℕ, 0 < k ∧
        x + (2 * k : ℝ) • Pi.single e₀ 1 ∈ parityPoints G ∧
        objective c (x + (2 * k : ℝ) • Pi.single e₀ 1) < M) := by sorry

end ChinesePostman.Polyhedron

