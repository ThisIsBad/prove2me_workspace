import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_ArgMin
import Definitions.Def_DiscreteConvex_AlgorithmsC_SBF
import Definitions.Def_DiscreteConvex_AlgorithmsC_IsMinimalMinimizerWT
import Definitions.Def_DiscreteConvex_AlgorithmsC_RhoP

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.30 (p.306). In the steepest descent algorithm with the minimal-minimizer
tie-breaking rule (10.33), `p ≤ p*` implies `p+χ_X ≤ p*` for the minimal minimizer `X` of `ρ_p`,
where `p*` is any minimizer of `g`. -/
theorem steepest_descent_monotone (g : (V → ℤ) → WithTop ℝ) (hg : SBF g) (p pstar : V → ℤ)
    (hpstar : pstar ∈ ArgMin g) (hple : ∀ v, p v ≤ pstar v) (X : Finset V)
    (hX : IsMinimalMinimizerWT (RhoP g p) X) :
    ∀ v, p v + (if v ∈ X then (1:ℤ) else 0) ≤ pstar v := by sorry

end DiscreteConvex.AlgorithmsC
