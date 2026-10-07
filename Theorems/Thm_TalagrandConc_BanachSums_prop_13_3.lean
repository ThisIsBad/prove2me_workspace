import Mathlib
import Definitions.Def_Komlos_RandomSignModel
import Definitions.Def_TalagrandConc_BanachSums_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.BanachSums

theorem prop_13_3 {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {N : ℕ} (q : ℕ) (hq : 2 ≤ q) (b : ℝ) (hb : 0 < b)
    (x : Fin N → W) (u : ℝ) (hu : 0 < u) :
    Komlos.spMeasure N
        {ε | 2 * Eeps x + u + topSumE x (kSigma q b x) ≤ ‖signedSum ε x‖}
      ≤ ENNReal.ofReal (4 * Real.exp (-(u ^ 2 / (16 * q * b ^ 2)))) := by sorry

end TalagrandConc.BanachSums

