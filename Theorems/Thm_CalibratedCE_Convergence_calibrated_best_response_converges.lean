import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_BestReply
import Definitions.Def_CalibratedCE_Convergence_EmpDist

namespace CalibratedCE.Convergence

/-- Foster–Vohra (1997), Theorem 1, p. 44: if each player best-responds, through a stationary
deterministic best-reply function, to a forecast calibrated against the other player's plays,
then the distance from the empirical joint distribution `D_t` to the set of correlated
equilibria, `min_{D ∈ π(G)} max_{x, y} |D_t(x, y) - D(x, y)|`, tends to `0`. -/
theorem calibrated_best_response_converges {m n : ℕ}
    (u₁ u₂ : Fin m → Fin n → ℝ)
    (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (hR₁ : IsBestReply₁ u₁ R₁) (hR₂ : IsBestReply₂ u₂ R₂)
    (f₁ : ℕ → Fin n → ℝ) (f₂ : ℕ → Fin m → ℝ)
    (hf₁ : ∀ t, IsDist (f₁ t)) (hf₂ : ∀ t, IsDist (f₂ t))
    (hcal₁ : Shared.Calibrated f₁ (fun s => R₂ (f₂ s)))
    (hcal₂ : Shared.Calibrated f₂ (fun s => R₁ (f₁ s))) :
    ∀ ε > 0, ∃ T : ℕ, ∀ t ≥ T, ∃ D : Fin m → Fin n → ℝ, IsCE u₁ u₂ D ∧
      ∀ a b, |empDist (fun s => R₁ (f₁ s)) (fun s => R₂ (f₂ s)) t a b - D a b| ≤ ε := by sorry

end CalibratedCE.Convergence
