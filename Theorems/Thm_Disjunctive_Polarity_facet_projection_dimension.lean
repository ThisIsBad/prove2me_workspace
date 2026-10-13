import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_EqualitySubsystem

namespace Disjunctive.Polarity

/-- Corollary 2.8 (Balas §2.2.3, p. 30): the dimension of the projection of a facet `FQ` of `Q`,
in terms of the dimension of `Proj_x(Q)` and the ranks `r*_F`, `r*` of the `u`-columns of `FQ`'s
and `Q`'s own equality subsystems. -/
theorem facet_projection_dimension {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (α : Fin p → ℝ) (β : Fin q → ℝ) (β0 : ℝ)
    (hFacet : IsFacet (Poly2 A B b) (FacetCandidate A B b α β β0)) :
    PolyDim (ProjOntoX (FacetCandidate A B b α β β0)) =
      PolyDim (ProjOntoX (Poly2 A B b)) - 1 +
        ((SystemRankA (Fin.cons α A)
            (TightRows (Fin.cons α A) (Fin.cons β B) (Fin.cons β0 b)
              (FacetCandidate A B b α β β0)) : ℤ) -
          (EqRankA A B b : ℤ)) := by sorry

end Disjunctive.Polarity

