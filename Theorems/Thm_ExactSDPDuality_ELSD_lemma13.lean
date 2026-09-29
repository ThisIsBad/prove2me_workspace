import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

/-- Lemma 13 (Ramana 1997, p. 143): if `0 ∈ G`, then `G° = Cl(G*)`. -/
theorem lemma13 {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm)
    (h0 : (0 : Fin m → ℝ) ∈ feasibleSet Q0 Q) :
    polar (feasibleSet Q0 Q) = closure (algPolar Q0 Q) := by sorry

end ExactSDPDuality.ELSD
