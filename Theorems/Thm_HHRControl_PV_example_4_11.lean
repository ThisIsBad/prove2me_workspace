import Mathlib
import Definitions.Def_HHRControl_PV_Elections

namespace HHRControl.PV

open Finset

/-- Example 4.11, p. 13: approval voting is susceptible to destructive control by partition of
voters, in models TE and TP. Candidates `a, b, c` are `0, 1, 2`; an approval ballot is the set of
approved candidates. -/
theorem example_4_11 :
    (let P : Fin 10 → Approval 3 :=
        ![{2}, {2}, {2}, {2}, {0}, {0}, {0}, {1}, {1}, {1}];
      approval.winners 3 10 P univ univ = {2} ∧
      approval.winners 3 10 P univ {0, 1, 4, 5, 6} = {0} ∧
      approval.winners 3 10 P univ ({0, 1, 4, 5, 6} : Finset (Fin 10))ᶜ = {1} ∧
      ∀ rule : TieRule, twoStage rule approval P {0, 1, 4, 5, 6} = {0, 1}) ∧
    SusceptibleDC .TE approval ∧ SusceptibleDC .TP approval := by sorry

end HHRControl.PV

