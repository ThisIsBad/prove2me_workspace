import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model

namespace MillerTuckerZemlin.Formulation

theorem objective_eq_itineraryLength (n p : ℕ) (d : Fin (n + 1) → Fin (n + 1) → ℝ)
    (I : Itinerary n) (hI : IsItinerary n p I) :
    objective d (arcCount I) = itineraryLength d I := by sorry

end MillerTuckerZemlin.Formulation

