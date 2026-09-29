import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_BestReply
import Definitions.Def_CalibratedCE_Convergence_EmpDist

open Filter Topology

namespace CalibratedCE.Convergence

/-- Proof of Theorem 1, p. 45: if player 1 best-responds to forecasts calibrated against player
2's plays `y`, then along any subsequence on which the empirical joint distribution converges
to `D`, every row `a` of `D` with positive mass, normalized, lies in `M_b(a)`. -/
theorem limit_conditional_mem_Mb {m n : ℕ} (u₁ : Fin m → Fin n → ℝ)
    (R₁ : (Fin n → ℝ) → Fin m) (hR₁ : IsBestReply₁ u₁ R₁)
    (f₁ : ℕ → Fin n → ℝ) (hf₁ : ∀ s, IsDist (f₁ s)) (y : ℕ → Fin n)
    (hcal : Shared.Calibrated f₁ y) (φ : ℕ → ℕ) (hφ : StrictMono φ) (D : Fin m → Fin n → ℝ)
    (hD : ∀ a b, Tendsto (fun i => empDist (fun s => R₁ (f₁ s)) y (φ i) a b) atTop
      (𝓝 (D a b)))
    (a : Fin m) (ha : 0 < ∑ c, D a c) :
    (fun b => D a b / ∑ c, D a c) ∈ Mb u₁ a := by sorry

end CalibratedCE.Convergence
