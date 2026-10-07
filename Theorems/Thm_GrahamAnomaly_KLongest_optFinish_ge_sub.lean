import Mathlib
import Definitions.Def_GrahamAnomaly_KLongest_Model

namespace GrahamAnomaly.KLongest

theorem optFinish_ge_sub {r n k : ℕ} (hn : 0 < n)
    (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (L : Fin r ≃ Fin r) (σ : Fin r → Fin n)
    (hσ : IsListAssignment μ L σ) (hkr : k < r)
    (hgt : prefixFinish μ L σ k < WilliamsonShmoys.makespan μ σ) :
    WilliamsonShmoys.makespan μ σ - ((n : ℝ) - 1) / n * alphaStar μ L k ≤
      optFinish μ n := by sorry

end GrahamAnomaly.KLongest

