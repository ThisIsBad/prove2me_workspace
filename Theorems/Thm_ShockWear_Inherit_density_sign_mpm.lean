import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

namespace ShockWear.Inherit

/-- The final sign-change assertion in the proof of (3.1), p. 633. -/
theorem density_sign_mpm (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 = 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hpf : IsPF2SeqFrom 1 (failProb P)) :
    ∀ c θ : ℝ, 0 < c → 0 < θ →
      SignMPM (fun t => shockDens lam P t - c * Real.exp (-(θ * t))) (Set.Ioi 0) := by sorry

end ShockWear.Inherit

