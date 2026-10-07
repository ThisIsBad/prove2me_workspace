import Mathlib
import Definitions.Def_GrahamAnomaly_KLongest_Model

namespace GrahamAnomaly.KLongest

theorem sum_div_le_optFinish {r n : ℕ} (hn : 0 < n) (μ : Fin r → ℝ)
    (hμ : ∀ j, 0 < μ j) :
    (1 / (n : ℝ)) * ∑ j, μ j ≤ optFinish μ n := by sorry

end GrahamAnomaly.KLongest

