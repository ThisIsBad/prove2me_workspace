import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

/-- Cachon (2003), 3rd draft, §6.6.1, p. 67 (the margin display). With a coordinating contract
(`λ ∈ [0, 1]`, `w_2 − b = λc_2`, `w_1 − w_2 + λc_2 = λc_1`) the supplier's period-2 margin is
`w_2 − c_2 = w_1 − (λc_1 + (1 − λ)c_2)`; it is strictly below the period-1 margin `w_1 − c_1` when
`λ < 1` and equal to it when `λ = 1`. -/
theorem p67_margin (M : Model) (lam w1 w2 b : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 - b = lam * M.c2)
    (hw1 : w1 - w2 + lam * M.c2 = lam * M.c1) :
    w2 - M.c2 = w1 - (lam * M.c1 + (1 - lam) * M.c2) ∧
    (lam < 1 → w2 - M.c2 < w1 - M.c1) ∧
    (lam = 1 → w2 - M.c2 = w1 - M.c1) := by sorry

end CachonCoord.DemandUpdate

