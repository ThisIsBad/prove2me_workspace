import Mathlib
import Definitions.Def_AccelScal_UCRace_Setting

noncomputable section

namespace AccelScal.UCRace

/-- Lin, Lemma 2 and equation (9), p. 7, with the random discovery times
integrated against their independent exponential joint law. -/
theorem lemma_2 (T1 T2 : Tech) (h1 : T1.Standing) (h2 : T2.Standing)
    (r : ℝ) (hr : 0 < r) (R1 R2 : ℝ) (hR1 : 0 < R1) (hR2 : 0 < R2) :
    payoff1 T1 T2 r R1 R2 = V1 T1 T2 r R1 R2 ∧
      payoff2 T1 T2 r R1 R2 =
        (T2.u R2 * T2.lam R2 - R2) / (r + T1.lam R1 + T2.lam R2) := by sorry

end AccelScal.UCRace

