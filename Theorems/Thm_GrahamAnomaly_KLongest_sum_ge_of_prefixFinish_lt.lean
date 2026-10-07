import Mathlib
import Definitions.Def_GrahamAnomaly_KLongest_Model

namespace GrahamAnomaly.KLongest

theorem sum_ge_of_prefixFinish_lt {r n k : ℕ} (hn : 0 < n)
    (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (L : Fin r ≃ Fin r) (σ : Fin r → Fin n)
    (hσ : IsListAssignment μ L σ) (hkr : k < r)
    (hgt : prefixFinish μ L σ k < WilliamsonShmoys.makespan μ σ) :
    (n : ℝ) * (WilliamsonShmoys.makespan μ σ - alphaStar μ L k) +
      alphaStar μ L k ≤ ∑ j, μ j := by sorry

end GrahamAnomaly.KLongest

