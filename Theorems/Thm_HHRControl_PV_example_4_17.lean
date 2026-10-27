import Mathlib
import Definitions.Def_HHRControl_PV_Elections

namespace HHRControl.PV

open Finset

/-- Example 4.17, p. 15: approval voting is susceptible to constructive control by partition of
voters, in models TE and TP. Candidates `a, b, c` are `0, 1, 2`; an approval ballot is the set of
approved candidates. -/
theorem example_4_17 :
    (let P : Fin 8 → Approval 3 := ![{0}, {0}, {0}, {1}, {1}, {2}, {2}, {2}];
      approval.winners 3 8 P univ univ = {0, 2} ∧
      approval.winners 3 8 P univ {0, 1, 5, 6, 7} = {2} ∧
      approval.winners 3 8 P univ ({0, 1, 5, 6, 7} : Finset (Fin 8))ᶜ = {1} ∧
      ∀ rule : TieRule, twoStage rule approval P {0, 1, 5, 6, 7} = {2}) ∧
    SusceptibleCC .TE approval ∧ SusceptibleCC .TP approval := by sorry

end HHRControl.PV

