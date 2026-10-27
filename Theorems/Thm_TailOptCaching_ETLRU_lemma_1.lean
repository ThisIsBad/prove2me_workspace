import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Model

open scoped ENNReal

namespace TailOptCaching.ETLRU

theorem lemma_1 (P : Params) (hξ : ∃ m : ℕ, P.ξ = m) (s : State) (hs : WellFormed P s)
    (θ q a : ℕ) (hθ : θ ≤ s.n) (z : State)
    (hz : GreedyRun P
      ((∑ i ∈ Finset.range (nAfter s θ), Function.update s.X θ (s.L θ + q + a) i) - P.C)
      (post P s θ q a (Function.update s.X θ (s.L θ + q + a))) z) :
    Feasible P s θ q a z.X ∧
      ∀ Y, Feasible P s θ q a Y → nextTEL P z ≤ nextTEL P (post P s θ q a Y) := by sorry

end TailOptCaching.ETLRU

