import Mathlib

namespace ConeLifts.NonnegRank

/-- The **face lattice** `L(C)` of a polytope `C ⊆ ℝⁿ` (Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, §4.2, p. 15): the faces of `C` ordered by inclusion. A face is an exposed face in
Mathlib's sense (`IsExposed ℝ C F`: `F` is empty or `F = {x ∈ C | l x = max_C l}` for a continuous
linear functional `l`); for a polytope every face is exposed. The empty face and `C` itself (via
`l = 0`) are faces, as in the paper's face counts (a square has 10 faces, a 3-cube 28, p. 16).
The order is inclusion of the underlying sets (the subtype order of `Set`). -/
def Face {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : Type :=
  {F : Set (EuclideanSpace ℝ (Fin n)) // IsExposed ℝ C F}

/-- Faces are ordered by inclusion. -/
instance {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : PartialOrder (Face C) :=
  inferInstanceAs (PartialOrder {F : Set (EuclideanSpace ℝ (Fin n)) // IsExposed ℝ C F})

end ConeLifts.NonnegRank
