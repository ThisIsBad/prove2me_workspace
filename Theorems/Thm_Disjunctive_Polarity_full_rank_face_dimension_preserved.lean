import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_EqualitySubsystem

namespace Disjunctive.Polarity

/-- Corollary 2.10 (Balas §2.2.3, p. 30): if `A=` has full column rank, every `d`-dimensional
face of `Q` (for `0 ≤ d ≤ dim(Q) - 1`) projects to a `d`-dimensional face of `Proj_x(Q)`. -/
theorem full_rank_face_dimension_preserved {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (hFullRank : EqRankA A B b = p)
    (Fc : Set ((Fin p → ℝ) × (Fin q → ℝ))) (hFace : IsExtreme ℝ (Poly2 A B b) Fc)
    (d : ℕ) (hd : (d : ℤ) ≤ PolyDim (Poly2 A B b) - 1) (hdimFc : PolyDim Fc = (d : ℤ)) :
    IsExtreme ℝ (ProjOntoX (Poly2 A B b)) (ProjOntoX Fc) ∧ PolyDim (ProjOntoX Fc) = (d : ℤ) := by sorry

end Disjunctive.Polarity

