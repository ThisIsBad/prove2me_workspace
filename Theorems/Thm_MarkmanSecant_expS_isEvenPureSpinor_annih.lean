import Mathlib
import Definitions.Def_MarkmanSecant

open MarkmanSecant
open scoped ExteriorAlgebra

namespace MarkmanSecant

theorem expS_isEvenPureSpinor_annih (n : ℕ) (Θ : Spinor n) (hΘ : Θ ∈ ⋀[ℂ]^2 (H1 n)) (c : ℂ) :
    IsEvenPureSpinor (expS (c • Θ)) ∧
      ∀ v : VC n, v ∈ annih (expS (c • Θ)) ↔ wPart v = -(c • theta Θ (tPart v)) := by sorry

end MarkmanSecant
