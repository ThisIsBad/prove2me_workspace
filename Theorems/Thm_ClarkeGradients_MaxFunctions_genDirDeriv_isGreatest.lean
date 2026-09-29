import Mathlib
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv

namespace ClarkeGradients.MaxFunctions

/-- Clarke (1975), Proposition (1.4): for locally Lipschitz `f`,
`f°(x; v) = max {ζ · v : ζ ∈ ∂f(x)}`, i.e. `f°(x; ·)` is the support function of `∂f(x)`. -/
theorem genDirDeriv_isGreatest {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Shared.LipschitzOnBounded f) (x v : EuclideanSpace ℝ (Fin n)) :
    IsGreatest ((fun ζ => inner ℝ ζ v) '' Shared.generalizedGradient f x) (Shared.genDirDeriv f x v) := by sorry

end ClarkeGradients.MaxFunctions
