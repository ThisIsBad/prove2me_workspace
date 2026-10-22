import Mathlib
import Definitions.Def_GeometryOfGraphs_FlowCut_Pseudometric

namespace GeometryOfGraphs.EuclidDist

/-- `(X, d)` embeds in a Euclidean space with distortion at most `c` (Definition 2.1, p. 218):
there are a dimension `m` and a map `φ : X → ℝ^m` (Euclidean norm) with
`‖φ x - φ y‖ ≤ d x y ≤ c * ‖φ x - φ y‖` for all `x, y`. -/
def EmbedsEuclidean {X : Type*} (d : X → X → ℝ) (c : ℝ) : Prop :=
  ∃ (m : ℕ) (φ : X → EuclideanSpace ℝ (Fin m)),
    ∀ x y, ‖φ x - φ y‖ ≤ d x y ∧ d x y ≤ c * ‖φ x - φ y‖

end GeometryOfGraphs.EuclidDist
