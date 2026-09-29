import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix Pointwise

namespace ExactSDPDuality.ELSD

/-- Corollary 14 (Ramana 1997, p. 144): if `0 ∈ G` and `T = {x | Ax = 0}` for a real
`r × m` matrix `A`, then `(G ∩ T)° = Cl(G* + T^⊥)` (Minkowski sum). -/
theorem cor14 {n m r : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm)
    (h0 : (0 : Fin m → ℝ) ∈ feasibleSet Q0 Q) (A : Matrix (Fin r) (Fin m) ℝ) :
    polar (feasibleSet Q0 Q ∩ {x | A *ᵥ x = 0}) =
      closure (algPolar Q0 Q + perp {x | A *ᵥ x = 0}) := by sorry

end ExactSDPDuality.ELSD
