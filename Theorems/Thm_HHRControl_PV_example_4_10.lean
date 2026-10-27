import Mathlib
import Definitions.Def_HHRControl_PV_Elections

namespace HHRControl.PV

open Finset

/-- Example 4.10, p. 12: Condorcet voting is susceptible to destructive control by partition of
voters (in either tie-handling model). Candidates `a, b, c` are `0, 1, 2`; a ballot is given by
its code, the candidates from the most to the least preferred. -/
theorem example_4_10 :
    (∀ P : Fin 7 → Ranking 3,
      (∀ v, rankingCode (P v) =
        ![[2, 0, 1], [2, 0, 1], [2, 1, 0], [1, 0, 2], [1, 2, 0], [0, 1, 2], [0, 2, 1]] v) →
        condorcet.winners 3 7 P univ univ = {2} ∧
        condorcet.winners 3 7 P univ {0, 6} = ∅ ∧
        condorcet.winners 3 7 P univ ({0, 6} : Finset (Fin 7))ᶜ = {1} ∧
        ∀ rule : TieRule, twoStage rule condorcet P {0, 6} ≠ {2}) ∧
    ∀ rule : TieRule, SusceptibleDC rule condorcet := by sorry

end HHRControl.PV

