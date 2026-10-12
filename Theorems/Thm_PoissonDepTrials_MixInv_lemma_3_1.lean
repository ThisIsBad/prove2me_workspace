import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem lemma_3_1 (lam : ℝ) (w : ℕ) (hw : 1 ≤ w) (hlw : (w : ℝ) ≤ lam) :
    ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * ∑ k ∈ Finset.range w, lam ^ k / (k.factorial : ℝ)
      ≤ 2 / Real.sqrt lam := by sorry

end PoissonDepTrials.MixInv

