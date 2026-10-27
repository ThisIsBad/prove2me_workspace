import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

namespace WHAdditivity.Renyi

theorem trace_marginal_product (N : ℕ) (d : Fin N → ℕ) (ρ : Matrix (Config d) (Config d) ℂ)
    (Λ Λ' : Finset (Fin N)) :
    (tensorIdentity d Λ (reducedMatrix d Λ ρ) * tensorIdentity d Λ' (reducedMatrix d Λ' ρ)).trace =
      (∏ j ∈ (Λ ∪ Λ')ᶜ, (d j : ℂ)) * (reducedMatrix d (Λ ∩ Λ') ρ ^ 2).trace := by sorry

end WHAdditivity.Renyi

