import Mathlib
import Definitions.Def_ConeLifts_Shared_polar

open scoped InnerProductSpace

namespace ConeLifts.StableSet

/-- The **canonical slack matrix** `S_P` of a polytope `P ⊆ ℝⁿ` with the origin in its interior
(Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, §3, p. 9, Definition 3.1 and the paragraph after
it): rows are indexed by the vertices `ext(P)`, columns by `ext(P°)` (which are in bijection with
the facets of `P`), and the entry at `(p, y)` is `h_y(p) = 1 - ⟨p, y⟩`, the value at `p` of the
canonical (normalized `h(0) = 1`) facet inequality attached to `y`. -/
noncomputable def canonicalSlackMatrix {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) :
    Matrix (Set.extremePoints ℝ P) (Set.extremePoints ℝ (ConeLifts.Shared.polar P)) ℝ :=
  fun p y => 1 - ⟪(p : EuclideanSpace ℝ (Fin n)), (y : EuclideanSpace ℝ (Fin n))⟫_ℝ

/-- `M` is **a slack matrix** of the polytope `P` (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2,
Definition 3.1, p. 9): the matrix `(h_j(p_i))` of a facet inequality representation
`P = {x : h₁(x) ≥ 0, …, h_f(x) ≥ 0}`. Each facet inequality is determined up to a positive
scalar (p. 9), so the slack matrices of `P` are exactly the canonical slack matrix with every
column multiplied by a positive scalar ("any slack matrix of P can be obtained from the canonical
one by multiplication by a diagonal nonnegative matrix", p. 9); rows and columns are indexed by
the vertices of `P` and the extreme points of `P°` instead of by `1, …, v` and `1, …, f`. -/
def IsSlackMatrix {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (M : Matrix (Set.extremePoints ℝ P) (Set.extremePoints ℝ (ConeLifts.Shared.polar P)) ℝ) : Prop :=
  ∃ w : Set.extremePoints ℝ (ConeLifts.Shared.polar P) → ℝ, (∀ y, 0 < w y) ∧
    ∀ p y, M p y = w y * canonicalSlackMatrix P p y

end ConeLifts.StableSet
