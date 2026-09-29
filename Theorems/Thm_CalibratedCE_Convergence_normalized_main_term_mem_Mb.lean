import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_BestReply

namespace CalibratedCE.Convergence

/-- Proof of Theorem 1, p. 45: the `N`-weighted average of the issued forecasts at which player 1
plays `a` lies in `M_b(a)`. -/
theorem normalized_main_term_mem_Mb {m n : ℕ} (u₁ : Fin m → Fin n → ℝ)
    (R₁ : (Fin n → ℝ) → Fin m) (hR₁ : IsBestReply₁ u₁ R₁)
    (f₁ : ℕ → Fin n → ℝ) (hf₁ : ∀ s, IsDist (f₁ s)) (t : ℕ) (a : Fin m)
    (hpos : 0 < ∑ q ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
      (Shared.N f₁ q t : ℝ)) :
    (fun b => ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
        p b * (Shared.N f₁ p t : ℝ) /
          ∑ q ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a), (Shared.N f₁ q t : ℝ))
      ∈ Mb u₁ a := by sorry

end CalibratedCE.Convergence
