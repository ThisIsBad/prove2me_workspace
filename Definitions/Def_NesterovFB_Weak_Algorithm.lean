import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Rates_Algorithm

namespace NesterovFB.Weak

/-- The quantity of the proof of Theorem 3:
δ_k = (k − 1)(‖x_k − x*‖² − ‖x_{k−1} − x*‖²) + (α − 1)‖x_k − x*‖². -/
noncomputable def deltaSeq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (α : ℝ) (x : ℕ → H) (xstar : H) (k : ℕ) : ℝ :=
  ((k : ℝ) - 1) * (‖x k - xstar‖ ^ 2 - ‖x (k - 1) - xstar‖ ^ 2) + (α - 1) * ‖x k - xstar‖ ^ 2

end NesterovFB.Weak
