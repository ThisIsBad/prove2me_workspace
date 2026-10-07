import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model

namespace MillerTuckerZemlin.Formulation

theorem mtz_formulation_equivalent (n p : ℕ) (hp : 1 ≤ p) :
    (∀ (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ), Feasible n p x u →
        ∃ I : Itinerary n, IsItinerary n p I ∧ x = arcCount I ∧
          ∑ i ∈ Finset.univ.filter (· ≠ (0 : Fin (n + 1))), x i 0 = I.length) ∧
    (∀ I : Itinerary n, IsItinerary n p I →
        (∃ u : Fin (n + 1) → ℕ, Feasible n p (arcCount I) (fun i => (u i : ℝ))) ∧
          ∑ i ∈ Finset.univ.filter (· ≠ (0 : Fin (n + 1))), arcCount I i 0 = I.length) ∧
    (∀ (d : Fin (n + 1) → Fin (n + 1) → ℝ) (I : Itinerary n), IsItinerary n p I →
        objective d (arcCount I) = itineraryLength d I) := by sorry

end MillerTuckerZemlin.Formulation

