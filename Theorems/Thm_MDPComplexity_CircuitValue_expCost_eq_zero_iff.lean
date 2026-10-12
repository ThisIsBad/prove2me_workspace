import Mathlib
import Definitions.Def_MDPComplexity_CircuitValue_Model

namespace MDPComplexity.CircuitValue

open Finset BigOperators

theorem expCost_eq_zero_iff {S : Type} [Fintype S] [DecidableEq S] (M : MDP S)
    (hc : ∀ s i t, 0 ≤ M.c s i t) (s₀ : S) (δ : M.Policy) (T : ℕ) :
    M.expCost s₀ δ T = 0 ↔
      ∀ x : Fin (T + 1) → S, 0 < M.trajProb s₀ δ T x →
        ∀ t : Fin (T + 1), M.c (x t) (δ (x t) (t : ℕ)) (t : ℕ) = 0 := by sorry

end MDPComplexity.CircuitValue

