import Mathlib
import Definitions.Def_GrahamAnomaly_KLongest_Model

namespace GrahamAnomaly.KLongest

theorem eq_optFinish_of_eq_prefixFinish {r n k : ℕ} (hr : 0 < r) (hn : 0 < n)
    (hk : k ≤ r) (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (L : Fin r ≃ Fin r) (σ : Fin r → Fin n)
    (hlong : ∀ i j, (L.symm i : ℕ) < k → k ≤ (L.symm j : ℕ) → μ j ≤ μ i)
    (hσ : IsListAssignment μ L σ)
    (hopt : ∀ τ : Fin r → Fin n, prefixFinish μ L σ k ≤ prefixFinish μ L τ k) :
    WilliamsonShmoys.makespan μ σ = prefixFinish μ L σ k →
      WilliamsonShmoys.makespan μ σ = optFinish μ n := by sorry

end GrahamAnomaly.KLongest

