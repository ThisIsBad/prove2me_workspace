import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Factorization_IsClosedConvexCone
import Definitions.Def_ConeLifts_Factorization_HasLift
import Definitions.Def_ConeLifts_Factorization_HasProperLift
import Definitions.Def_ConeLifts_Factorization_SlackFactorizable

namespace ConeLifts.Factorization

/-- **Theorem 2.4** of Gouveia, Parrilo & Thomas, *Lifts of Convex Sets and Cone Factorizations*,
arXiv:1111.3164v2, p. 4: "If C has a proper K-lift then S_C is K-factorizable. Conversely, if S_C
is K-factorizable then C has a K-lift."

Standing hypotheses (Definition 2.1, p. 3): `K ⊆ ℝᵐ` is a full-dimensional closed convex cone and
`C ⊆ ℝⁿ` is a convex body (compact, convex, `0 ∈ int C`). `1 ≤ n` is the paper's implicit
"full-dimensional convex body in ℝⁿ": for `n = 0` the first half is false. The converse
concludes a `K`-lift that need not be proper. -/
theorem factorization_theorem {n m : ℕ} (hn : 1 ≤ n)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsConvexBody C)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (hKint : (interior K).Nonempty) :
    (HasProperLift K C → SlackFactorizable K C) ∧ (SlackFactorizable K C → HasLift K C) := by sorry

end ConeLifts.Factorization

