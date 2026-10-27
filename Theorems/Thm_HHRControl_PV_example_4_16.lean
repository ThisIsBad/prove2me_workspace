import Mathlib
import Definitions.Def_HHRControl_PV_Elections

namespace HHRControl.PV

open Finset

/-- Example 4.16, p. 14: plurality voting is susceptible to constructive and to destructive control
by partition of voters in model TP. Candidates `a, b, c` are `0, 1, 2`; a ballot is given by its
code, the candidates from the most to the least preferred. The voters are listed in the order
`u₁, u₂, u₃, v₁, v₂, w₁, w₂, w₃` (then `v₃, w₄` for the election `(C, V′)`). -/
theorem example_4_16 :
    (∀ P : Fin 8 → Ranking 3,
      (∀ v, rankingCode (P v) = ![[0, 2, 1], [0, 2, 1], [0, 2, 1], [1, 0, 2], [1, 0, 2],
          [2, 0, 1], [2, 0, 1], [2, 0, 1]] v) →
        plurality.winners 3 8 P univ univ = {0, 2} ∧
        plurality.winners 3 8 P univ {0, 1, 5, 6, 7} = {2} ∧
        plurality.winners 3 8 P univ ({0, 1, 5, 6, 7} : Finset (Fin 8))ᶜ = {1} ∧
        twoStage .TP plurality P {0, 1, 5, 6, 7} = {2}) ∧
    (∀ P' : Fin 10 → Ranking 3,
      (∀ v, rankingCode (P' v) = ![[0, 2, 1], [0, 2, 1], [0, 2, 1], [1, 0, 2], [1, 0, 2],
          [2, 0, 1], [2, 0, 1], [2, 0, 1], [1, 0, 2], [2, 0, 1]] v) →
        plurality.winners 3 10 P' univ univ = {2} ∧
        plurality.winners 3 10 P' univ {0, 1, 2, 5, 6} = {0} ∧
        plurality.winners 3 10 P' univ ({0, 1, 2, 5, 6} : Finset (Fin 10))ᶜ = {1} ∧
        twoStage .TP plurality P' {0, 1, 2, 5, 6} = {0}) ∧
    SusceptibleCC .TP plurality ∧ SusceptibleDC .TP plurality := by sorry

end HHRControl.PV

