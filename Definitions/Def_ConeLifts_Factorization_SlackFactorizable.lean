import Mathlib
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_Shared_dualCone

open scoped InnerProductSpace

namespace ConeLifts.Factorization

/-- The **slack operator `S_C` of `C` is `K`-factorizable** (Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, §2 p. 3 and Definition 2.2, p. 4). The slack operator is the restriction of
`S(x, y) = 1 - ⟨x, y⟩` to `ext(C) × ext(C°)`; it is `K`-factorizable if there are maps (not
necessarily linear) `A : ext(C) → K` and `B : ext(C°) → K*` with `S_C(x, y) = ⟨A(x), B(y)⟩` for
all `(x, y) ∈ ext(C) × ext(C°)`.

`A` and `B` are total functions `ℝⁿ → ℝᵐ` constrained only on `ext(C)` resp. `ext(C°)`; their
values elsewhere are irrelevant, so this is equivalent to maps defined on the extreme points
only. `ext` is Mathlib's `Set.extremePoints ℝ`, `C°` is the one-sided `polar`, `K*` is
`dualCone K`, and both pairings are the Euclidean inner product. -/
def SlackFactorizable {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ A B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m),
    (∀ x ∈ Set.extremePoints ℝ C, A x ∈ K) ∧
    (∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), B y ∈ ConeLifts.Shared.dualCone K) ∧
    ∀ x ∈ Set.extremePoints ℝ C, ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C),
      1 - ⟪x, y⟫_ℝ = ⟪A x, B y⟫_ℝ

end ConeLifts.Factorization
