import Mathlib
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_NonnegRank_slackOperator

namespace ConeLifts.NonnegRank

/-- The slack operator of `C` has an **`ℝᵏ₊`-factorization** (Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, Definition 2.2 with `K = ℝᵏ₊ = K*`, and Definition 4.3, p. 13): there are maps
`A : ext(C) → ℝᵏ₊` and `B : ext(C°) → ℝᵏ₊` (not necessarily linear) with
`S_C(x, y) = 1 − ⟨x, y⟩ = ⟨A(x), B(y)⟩` for all `x ∈ ext(C)`, `y ∈ ext(C°)`.
`A`, `B` are total functions on `ℝⁿ`; only their values on the extreme points are constrained. -/
def HasNonnegFactorization {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Prop :=
  ∃ A B : EuclideanSpace ℝ (Fin n) → (Fin k → ℝ),
    (∀ x ∈ Set.extremePoints ℝ C, ∀ i, 0 ≤ A x i) ∧
    (∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), ∀ i, 0 ≤ B y i) ∧
    ∀ x ∈ Set.extremePoints ℝ C, ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C),
      slackOperator x y = ∑ i, A x i * B y i

/-- The **nonnegative rank** `rank₊(C)` of a convex body `C` (Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, Definition 4.3 (2) with `K = (ℝⁱ₊)`, p. 13): the smallest `i` such that the slack
operator `S_C` has an `ℝⁱ₊`-factorization, and `+∞` (`⊤ : ℕ∞`) if no such `i` exists. -/
noncomputable def nonnegRank {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : HasNonnegFactorization C k), (k : ℕ∞)

end ConeLifts.NonnegRank
