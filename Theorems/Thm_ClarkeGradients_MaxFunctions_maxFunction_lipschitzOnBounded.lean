import Mathlib
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_ClarkeGradients_MaxFunctions_maxFunction

namespace ClarkeGradients.MaxFunctions

/-- Clarke (1975), Theorem (2.1), assertion (1): if `U` is a nonempty sequentially compact
space, `g(x, u)` is upper semicontinuous in `(x, u)` (hypothesis (a)) and `g` is locally
Lipschitz in `x` uniformly for `u ∈ U` (hypothesis (b)), then `f(x) = max_u g(x, u)` is
locally Lipschitz. -/
theorem maxFunction_lipschitzOnBounded
    {n : ℕ} {U : Type*} [TopologicalSpace U] [SeqCompactSpace U] [Nonempty U]
    (g : EuclideanSpace ℝ (Fin n) → U → ℝ)
    (ha : UpperSemicontinuous (fun p : EuclideanSpace ℝ (Fin n) × U => g p.1 p.2))
    (hb : ∀ B : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded B →
      ∃ K : NNReal, ∀ u : U, LipschitzOnWith K (fun y => g y u) B) :
    Shared.LipschitzOnBounded (maxFunction g) := by sorry

end ClarkeGradients.MaxFunctions
