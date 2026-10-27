import Mathlib
import Definitions.Def_OSPMech_SqrtLB_Model

namespace OSPMech.SqrtLB
theorem theorem_3 {n : ℕ} {X : Type} (D : Fin n → Finset ℝ) (cost : Fin n → ℝ → X → ℝ)
    (t : ImplTree n X) :
    (∃ p : (Fin n → ℝ) → Fin n → ℝ, IsOSP D cost t p) ↔ ∀ i, NoNegCycle D cost t i := by sorry
end OSPMech.SqrtLB

