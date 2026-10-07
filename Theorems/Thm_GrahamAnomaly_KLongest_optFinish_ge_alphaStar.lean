import Mathlib
import Definitions.Def_GrahamAnomaly_KLongest_Model

namespace GrahamAnomaly.KLongest

theorem optFinish_ge_alphaStar {r n k : ℕ} (hn : 0 < n) (hk : k ≤ r)
    (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (L : Fin r ≃ Fin r)
    (hlong : ∀ i j, (L.symm i : ℕ) < k → k ≤ (L.symm j : ℕ) → μ j ≤ μ i)
    (hkr : k < r) :
    (1 + ((k / n : ℕ) : ℝ)) * alphaStar μ L k ≤ optFinish μ n := by sorry

end GrahamAnomaly.KLongest

