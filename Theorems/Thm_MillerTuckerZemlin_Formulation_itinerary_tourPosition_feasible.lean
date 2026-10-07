import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model

namespace MillerTuckerZemlin.Formulation

theorem itinerary_tourPosition_feasible (n p : ℕ) (I : Itinerary n) (hI : IsItinerary n p I) :
    Feasible n p (arcCount I) (fun i => (tourPosition I i : ℝ)) ∧
      ∀ i : Fin (n + 1), i ≠ 0 → 1 ≤ tourPosition I i ∧ tourPosition I i ≤ p := by sorry

end MillerTuckerZemlin.Formulation

