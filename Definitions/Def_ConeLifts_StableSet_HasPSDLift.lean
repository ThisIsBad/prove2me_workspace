import Mathlib
import Definitions.Def_ConeLifts_StableSet_HasConeLift

namespace ConeLifts.StableSet

/-- The cone `Sᵏ₊` of `k × k` real symmetric positive semidefinite matrices (Gouveia, Parrilo &
Thomas, arXiv:1111.3164v2, §1, p. 1), as a subset of all real `k × k` matrices. Mathlib's
`Matrix.PosSemidef` includes symmetry (`Xᴴ = X`), so this set is exactly `Sᵏ₊`. -/
def psdCone (k : ℕ) : Set (Matrix (Fin k) (Fin k) ℝ) :=
  {X | X.PosSemidef}

/-- `C ⊆ ℝⁿ` **admits a `Sᵏ₊`-lift** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2,
Definition 2.1, p. 3, with `K = Sᵏ₊`): there are an affine subspace `L` of the space of real
`k × k` matrices and a linear map `π` from that space to `ℝⁿ` with `C = π(Sᵏ₊ ∩ L)`.

The ambient space is all `k × k` matrices rather than the symmetric ones. Existence of a lift is
unaffected: a lift in the symmetric matrices extends (same `L`, `π` extended linearly), and a
lift in all matrices restricts (intersect `L` with the symmetric matrices, which contain
`Sᵏ₊`, and restrict `π`). -/
def HasPSDLift (k : ℕ) {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  HasConeLift (psdCone k) C

end ConeLifts.StableSet
