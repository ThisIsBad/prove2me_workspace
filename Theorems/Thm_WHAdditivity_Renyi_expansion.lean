import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

namespace WHAdditivity.Renyi

theorem expansion (N : ℕ) (d : Fin N → ℕ) (hd : ∀ j, 2 ≤ d j) (Ω : Config d → ℂ)
    (hΩ : IsUnitVector Ω) :
    tensorChannel d (fun j => wernerHolevo (d j)) (pureState Ω) =
      (∏ j, ((d j : ℂ) - 1)⁻¹) • ∑ Λ : Finset (Fin N),
        ((-1 : ℂ) ^ Λ.card) • tensorIdentity d Λ (reducedMatrix d Λ (pureState (star Ω))) := by sorry

end WHAdditivity.Renyi

