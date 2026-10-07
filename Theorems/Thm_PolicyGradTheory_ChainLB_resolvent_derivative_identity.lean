import Mathlib
import Definitions.Def_PolicyGradTheory_ChainLB_Chain

namespace PolicyGradTheory.ChainLB

/-- Appendix B.2, (32), p. 54: derivative of one resolvent entry in an interior forward probability. -/
theorem resolvent_derivative_identity (H : ℕ) (hH : 1 ≤ H)
    (p : Fin H → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (a b : Fin (H + 2)) (i : Fin H) :
    fderiv ℝ (fun q : Fin H → ℝ => chainResolvent H q a b) p (Pi.single i (1 : ℝ)) =
      chainGamma H * chainResolvent H p a ⟨i.val + 1, by omega⟩ *
        (chainResolvent H p ⟨i.val + 2, by omega⟩ b -
         chainResolvent H p ⟨i.val, by omega⟩ b) := by sorry

end PolicyGradTheory.ChainLB

