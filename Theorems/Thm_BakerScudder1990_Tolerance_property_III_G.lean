import Mathlib
import Definitions.Def_BakerScudder1990_Tolerance_Instance

namespace BakerScudder1990.Tolerance

open Instance

/-- Property III(G) (Baker and Scudder 1990, p. 30; proof p. 34). For a fixed sequence of
`n > 0` jobs processed without inserted idle time, a least optimal common due date exists, and at
every least optimal due date `d` some job `k` completes at an end of its tolerance window:
`C_k = d - u_k` or `C_k = d + v_k`. -/
theorem property_III_G {n : ℕ} (I : Instance n) (hn : 0 < n) :
    (∃ d : ℝ, I.IsLeastOptimalDueDate d) ∧
      ∀ d : ℝ, I.IsLeastOptimalDueDate d →
        ∃ k : Fin n, I.C k = d - I.u k ∨ I.C k = d + I.v k := by sorry

end BakerScudder1990.Tolerance

