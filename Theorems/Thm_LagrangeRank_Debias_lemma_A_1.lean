import Mathlib
import Definitions.Def_LagrangeRank_Debias_Setting

namespace LagrangeRank.Debias
open Matrix
theorem lemma_A_1 (c1 c2 c3 L1 L2 : ℝ) (hc3 : 0 < c3) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (d : ℕ) (F f : (Fin d → ℝ) → ℝ) (OmHat OmStar : Matrix (Fin d) (Fin d) ℝ)
        (thetaHat thetaStar : Fin d → ℝ) (ρ1 ρ2 ρ3 ρ4 ρ5 : ℝ),
        ContDiff ℝ 2 F → ContDiff ℝ 1 f → f thetaStar = 0 →
        0 ≤ ρ1 → 0 ≤ ρ2 → 0 ≤ ρ3 → 0 ≤ ρ4 → 0 ≤ ρ5 → ρ1 + ρ4 ≤ δ →
        ‖thetaHat - thetaStar‖ ≤ ρ1 →
        ‖grad F thetaStar‖ ≤ ρ2 →
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          rowSumNorm (hess F (thetaStar + t • (thetaHat - thetaStar)) - hess F thetaStar)
            ≤ L1 * ‖(thetaStar + t • (thetaHat - thetaStar)) - thetaStar‖) →
        l1Norm (grad f thetaStar) ≤ c1 →
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          l1Norm (grad f (thetaStar + t • (thetaHat - thetaStar)) - grad f thetaStar)
            ≤ L2 * ‖(thetaStar + t • (thetaHat - thetaStar)) - thetaStar‖) →
        rowSumNorm (1 - OmHat * hess F thetaHat) ≤ ρ3 →
        rowSumNorm (OmHat - OmStar) ≤ ρ4 →
        rowSumNorm OmStar ≤ c2 →
        c3 ≤ grad f thetaStar ⬝ᵥ (OmStar *ᵥ grad f thetaStar) →
        rowSumNorm (thetaBlock OmStar (grad f thetaStar)) ≤ ρ5 →
        ‖fun k => remJ1 (thetaBlock OmHat (grad f thetaHat)) (thetaBlock OmStar (grad f thetaStar))
            (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar (Sum.inl k)‖
            ≤ C * ((ρ1 + ρ4) * (ρ1 ^ 2 + ρ2)) ∧
        ‖remJ2 (thetaBlock OmStar (grad f thetaStar))
            (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar‖
            ≤ C * (ρ1 ^ 2 * ρ5) ∧
        ‖fun k => remJ3 (thetaBlock OmHat (grad f thetaHat))
            (borderedHessian (hess F thetaHat) (grad f thetaHat)) thetaHat thetaStar (Sum.inl k)‖
            ≤ C * (ρ1 * ρ3) ∧
        ‖fun k => (remJ1 (thetaBlock OmHat (grad f thetaHat)) (thetaBlock OmStar (grad f thetaStar))
              (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar
            + remJ2 (thetaBlock OmStar (grad f thetaStar))
              (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar
            + remJ3 (thetaBlock OmHat (grad f thetaHat))
              (borderedHessian (hess F thetaHat) (grad f thetaHat)) thetaHat thetaStar) (Sum.inl k)‖
            ≤ C * (ρ1 ^ 2 * ρ5 + (ρ1 + ρ4) * (ρ1 ^ 2 + ρ2) + ρ1 * ρ3) := by sorry
end LagrangeRank.Debias

