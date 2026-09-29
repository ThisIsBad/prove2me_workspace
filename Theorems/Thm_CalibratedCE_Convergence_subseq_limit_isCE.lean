import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_BestReply
import Definitions.Def_CalibratedCE_Convergence_EmpDist

open Filter Topology

namespace CalibratedCE.Convergence

/-- Proof of Theorem 1, p. 44: under the hypotheses of Theorem 1, every subsequential limit of
the empirical joint distributions is a correlated equilibrium. -/
theorem subseq_limit_isCE {m n : ℕ}
    (u₁ u₂ : Fin m → Fin n → ℝ)
    (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (hR₁ : IsBestReply₁ u₁ R₁) (hR₂ : IsBestReply₂ u₂ R₂)
    (f₁ : ℕ → Fin n → ℝ) (f₂ : ℕ → Fin m → ℝ)
    (hf₁ : ∀ t, IsDist (f₁ t)) (hf₂ : ∀ t, IsDist (f₂ t))
    (hcal₁ : Shared.Calibrated f₁ (fun s => R₂ (f₂ s)))
    (hcal₂ : Shared.Calibrated f₂ (fun s => R₁ (f₁ s)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (D : Fin m → Fin n → ℝ)
    (hD : ∀ a b, Tendsto (fun i => empDist (fun s => R₁ (f₁ s)) (fun s => R₂ (f₂ s)) (φ i) a b)
      atTop (𝓝 (D a b))) :
    IsCE u₁ u₂ D := by sorry

end CalibratedCE.Convergence
