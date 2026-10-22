import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

namespace ShockWear.Inherit

/-- Theorem 3.1(3.1): discrete PF₂ failure probabilities give a PF₂ density. -/
theorem theorem31_1 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 = 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hpf : IsPF2SeqFrom 1 (failProb P)) :
    IsPF2Dens (shockDens lam P) := by sorry

end ShockWear.Inherit

