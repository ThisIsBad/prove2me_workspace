import Mathlib
import Definitions.Def_PolicyGradTheory_ChainLB_Chain

namespace PolicyGradTheory.ChainLB

/-- Appendix B.2, p. 51: the return from s₀ is the last-column resolvent entry. -/
theorem chain_value_eq_resolvent (H : ℕ) (hH : 1 ≤ H)
    (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hθ : ∀ i j, 0 < θ (i, j) ∧ θ (i, j) < 1)
    (hθ1 : ∀ i, θ (i, (0 : Fin 3)) < 1 / 4) :
    chainValue H θ = chainResolvent H (forwardProb H θ) 0 (Fin.last (H + 1)) := by sorry

end PolicyGradTheory.ChainLB

