import Mathlib
import Definitions.Def_HHRControl_PV_Elections

namespace HHRControl.PV

open Finset

/-- Example 4.9, p. 12: plurality voting is susceptible to constructive and to destructive control
by partition of voters in model TE. Candidates `a, b, c` are `0, 1, 2`; a ballot is given by its
code, the candidates from the most to the least preferred. -/
theorem example_4_9 :
    (∀ P : Fin 5 → Ranking 3,
      (∀ v, rankingCode (P v) = ![[0, 1, 2], [0, 1, 2], [1, 0, 2], [1, 0, 2], [2, 0, 1]] v) →
        (2 : Fin 3) ∉ plurality.winners 3 5 P univ univ ∧
        plurality.winners 3 5 P univ {4} = {2} ∧
        plurality.winners 3 5 P univ ({4} : Finset (Fin 5))ᶜ = {0, 1} ∧
        twoStage .TE plurality P {4} = {2}) ∧
    (∀ P' : Fin 4 → Ranking 3,
      (∀ v, rankingCode (P' v) = ![[0, 1, 2], [0, 1, 2], [1, 0, 2], [2, 0, 1]] v) →
        plurality.winners 3 4 P' univ univ = {0} ∧
        nominees .TE plurality P' {0, 2} = ∅ ∧
        nominees .TE plurality P' ({0, 2} : Finset (Fin 4))ᶜ = ∅ ∧
        twoStage .TE plurality P' {0, 2} ≠ {0}) ∧
    SusceptibleCC .TE plurality ∧ SusceptibleDC .TE plurality := by sorry

end HHRControl.PV

