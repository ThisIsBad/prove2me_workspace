import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_EqualitySubsystem

namespace Disjunctive.Polarity

/-- Corollary 2.9 (Balas §2.2.3, p. 30): the projection of a facet `FQ` of `Q` is itself a facet
of `Proj_x(Q)` if and only if `FQ`'s and `Q`'s equality-subsystem `u`-ranks agree. -/
theorem facet_projects_to_facet_iff {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (α : Fin p → ℝ) (β : Fin q → ℝ) (β0 : ℝ)
    (hFacet : IsFacet (Poly2 A B b) (FacetCandidate A B b α β β0)) :
    IsFacet (ProjOntoX (Poly2 A B b)) (ProjOntoX (FacetCandidate A B b α β β0)) ↔
      SystemRankA (Fin.cons α A)
          (TightRows (Fin.cons α A) (Fin.cons β B) (Fin.cons β0 b)
            (FacetCandidate A B b α β β0)) =
        EqRankA A B b := by sorry

end Disjunctive.Polarity

