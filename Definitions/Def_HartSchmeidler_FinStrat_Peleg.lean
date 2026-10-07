import Definitions.Def_HartSchmeidler_FinStrat_Game

/-! Peleg's examples in Hart and Schmeidler (1989), pp. 21–22. -/

namespace HartSchmeidler.FinStrat

open MeasureTheory

/-- Case 1: only finitely many positive-integer players choose action 1. -/
def pelegCase1 : Set (PNat → Fin 2) :=
  {s | {i : PNat | s i = 1}.Finite}

/-- Example 1 payoff: action 1 earns +1 in Case 1 and −1 otherwise. -/
noncomputable def pelegPayoff (i : PNat) (s : PNat → Fin 2) : ℝ := by
  classical
  exact if s ∈ pelegCase1 then (s i : ℕ) else -((s i : ℕ) : ℝ)

/-- Example 2 payoff: Case 1's reward for action 1 is 1/i². -/
noncomputable def peleg2Payoff (i : PNat) (s : PNat → Fin 2) : ℝ := by
  classical
  exact if s ∈ pelegCase1 then ((s i : ℕ) : ℝ) / ((i : ℕ) : ℝ) ^ 2
    else -((s i : ℕ) : ℝ)

end HartSchmeidler.FinStrat
