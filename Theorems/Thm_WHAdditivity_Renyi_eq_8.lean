import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

namespace WHAdditivity.Renyi

theorem eq_8 (N : ℕ) (d : Fin N → ℕ) (hd : ∀ j, 2 ≤ d j) (Ω : Config d → ℂ)
    (hΩ : IsUnitVector Ω) :
    let X := tensorChannel d (fun j => wernerHolevo (d j)) (pureState Ω)
    let ρ := pureState (star Ω)
    (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N), ∑ Λ' : Finset (Fin N),
          (-1 : ℂ) ^ (Λ.card + Λ'.card) *
            (tensorIdentity d Λ (reducedMatrix d Λ ρ) *
              tensorIdentity d Λ' (reducedMatrix d Λ' ρ)).trace ∧
    (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N), ∑ Λ' : Finset (Fin N),
          (-1 : ℂ) ^ (Λ.card + Λ'.card) *
            ((∏ j ∈ (Λ ∪ Λ')ᶜ, (d j : ℂ)) * (reducedMatrix d (Λ ∩ Λ') ρ ^ 2).trace) ∧
    (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N),
          (reducedMatrix d Λ ρ ^ 2).trace *
            ∑ Δ ∈ Λᶜ.powerset, (-1 : ℂ) ^ Δ.card *
              ∑ Δ' ∈ (Λᶜ \ Δ).powerset, (-1 : ℂ) ^ Δ'.card *
                ∏ j ∈ (Λᶜ \ Δ) \ Δ', (d j : ℂ) ∧
    (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N),
          (reducedMatrix d Λ ρ ^ 2).trace * ∏ j ∈ Λᶜ, ((d j : ℂ) - 2) ∧
    (X * X).trace.im = 0 ∧
    (X * X).trace.re ≤ ∏ j, ((d j : ℝ) - 1)⁻¹ := by sorry

end WHAdditivity.Renyi

