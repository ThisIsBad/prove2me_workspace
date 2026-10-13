import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_EqualitySubsystem

namespace Disjunctive.Polarity

/-- Theorem 2.7 (Balas §2.2.2, p. 29): the dimension of the projection of `Q` equals the
dimension of `Q`, minus the number of variables projected out, plus the rank of the `u`-columns
of `Q`'s equality subsystem. -/
theorem projection_dimension_formula {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (hQ : (Poly2 A B b).Nonempty) :
    PolyDim (ProjOntoX (Poly2 A B b)) = PolyDim (Poly2 A B b) - (p : ℤ) + (EqRankA A B b : ℤ) := by sorry

end Disjunctive.Polarity

