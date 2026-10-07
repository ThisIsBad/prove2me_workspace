import Mathlib
import Definitions.Def_ChinesePostman_Matching_Setting

namespace ChinesePostman.Matching


/-- §3, pp. 92–93: parity solutions and perfect matchings of odd nodes
have the same attained minimum cost. -/
theorem parity_problem_eq_odd_node_matching
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Connected G) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (d : V → V → ℝ) (hd : ∀ i j, IsShortestPathLength G c i j (d i j)) :
    (∃ f : V → V, IsOddPerfectMatching G f) ∧
    (∀ f : V → V, IsOddPerfectMatching G f →
      ∃ x : E → ℕ, IsParitySolution G x ∧ (∀ e, x e ≤ 1) ∧
        cost c x ≤ matchingLength G d f) ∧
    (∀ x : E → ℕ, IsParitySolution G x →
      ∃ f : V → V, IsOddPerfectMatching G f ∧
        matchingLength G d f ≤ cost c x) := by sorry
end ChinesePostman.Matching

