import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Remark 4 (p. 57). With finite mean trip lengths, for every open `s ⊆ (0, ∞)`:
`λ_{i→j}T_i(s) − Q_i(s) ≥ 0`, and it is maximized at `s = (0, ∞)`; `Q_i(s) ≥ 0`, and it is maximized at
`s = (0, ∞)`. -/
theorem remark_4 (P : Primitives) (hmean : FiniteMean P) (i : Fin 2) (s : Set ℝ)
    (hs : IsAdmissible s) :
    0 ≤ P.sw i * Tn P i s - Qn P i s ∧
    P.sw i * Tn P i s - Qn P i s ≤ P.sw i * Tn P i (Ioi 0) - Qn P i (Ioi 0) ∧
    0 ≤ Qn P i s ∧ Qn P i s ≤ Qn P i (Ioi 0) := by sorry

end DriverSurge.IC

