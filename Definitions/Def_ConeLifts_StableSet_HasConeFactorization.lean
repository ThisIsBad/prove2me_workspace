import Mathlib
import Definitions.Def_ConeLifts_Shared_dualCone

open scoped InnerProductSpace

namespace ConeLifts.StableSet

/-- A **`K`-factorization** of a matrix `M` (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2,
Definition 3.2, p. 9): vectors `aⁱ ∈ K` (one per row) and `bʲ ∈ K*` (one per column) with
`⟨aⁱ, bʲ⟩ = M_ij` for all `i, j`. Rows and columns are indexed by arbitrary types `ι`, `κ`
(for a slack matrix: the vertices of `P` and the extreme points of `P°`); `K*` is `dualCone K`
and the pairing is the Euclidean inner product of `EuclideanSpace ℝ (Fin m)`. -/
def HasConeFactorization {m : ℕ} {ι κ : Type*} (K : Set (EuclideanSpace ℝ (Fin m)))
    (M : Matrix ι κ ℝ) : Prop :=
  ∃ (a : ι → EuclideanSpace ℝ (Fin m)) (b : κ → EuclideanSpace ℝ (Fin m)),
    (∀ i, a i ∈ K) ∧ (∀ j, b j ∈ ConeLifts.Shared.dualCone K) ∧ ∀ i j, ⟪a i, b j⟫_ℝ = M i j

end ConeLifts.StableSet
