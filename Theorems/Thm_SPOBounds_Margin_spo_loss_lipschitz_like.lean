import Mathlib
import Definitions.Def_SPOBounds_Margin_Model
import Definitions.Def_SPOBounds_Margin_Degeneracy

namespace SPOBounds.Margin

/-- **Theorem 3(b)** (arXiv:1905.11488v3, p. 16). Under the strength property with parameter
`μ > 0` (nonempty, compact, convex, non-singleton `S`, any oracle `w`), for every fixed cost
vector `c` and all `ĉ₁, ĉ₂`,
`|ℓ_SPO(ĉ₁, c) − ℓ_SPO(ĉ₂, c)| ≤ (‖c‖_* / (μ · min{ν_S(ĉ₁), ν_S(ĉ₂)})) ‖ĉ₁ − ĉ₂‖_*`,
stated multiplied out (the paper reads the right-hand side as `+∞` when the minimum is `0`). -/
theorem spo_loss_lipschitz_like {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (hS : S.Nonempty) (hSc : IsCompact S) (hSv : Convex ℝ S) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (c c₁ c₂ : StrongDual ℝ E) :
    μ * min (nu S c₁) (nu S c₂) * |spoLoss w c₁ c - spoLoss w c₂ c| ≤
      ‖c‖ * ‖c₁ - c₂‖ := by sorry

end SPOBounds.Margin
