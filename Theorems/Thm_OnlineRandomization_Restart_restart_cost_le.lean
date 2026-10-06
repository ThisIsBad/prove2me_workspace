import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model
import Definitions.Def_OnlineRandomization_Restart_GameProperties
import Definitions.Def_OnlineRandomization_Restart_RestartAlgorithm

namespace OnlineRandomization.Restart

/-- p. 18: if `D` bounds the diameter, `f_0 ≤ H`, and `A_H` is `α`-competitive on `R_H`, then
on every nonempty `r` with segments `r(1), …, r(t)` the restart algorithm costs at most
`α(c(1)) + Σ_{i=2}^{t} (α(c(i)) + D)`. -/
theorem restart_cost_le {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (D H : ℝ)
    (hD : DiameterBound F D) (hf0 : F.cost [] [] ≤ H) (α : ℝ → ℝ) (AH : DetAlg R A)
    (hAH : ∀ r : List R, InRH F H r → AH.costOn F r ≤ α (F.opt r))
    (r : List R) (hr : r ≠ []) :
    (restart F H AH).costOn F r ≤
      ((segments F H r).map (fun s => α (F.opt s))).sum
        + (((segments F H r).length : ℝ) - 1) * D := by sorry

end OnlineRandomization.Restart

