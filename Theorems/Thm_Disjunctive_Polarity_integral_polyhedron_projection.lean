import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection

namespace Disjunctive.Polarity

/-- Proposition 2.6 (Balas §2.2, p. 28): the projection of an integral polyhedron is integral. -/
theorem integral_polyhedron_projection {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (hInt : IsIntegralPair (Poly2 A B b)) :
    IsIntegral (ProjOntoX (Poly2 A B b)) := by sorry

end Disjunctive.Polarity

