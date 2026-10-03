import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_DomZ
import Definitions.Def_DiscreteConvex_AlgorithmsC_LInftyNorm

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `K∞`, Eq. (10.38): the `ℓ∞`-size of `dom g`. -/
noncomputable def KInfty {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (g : (W → ℤ) → WithTop ℝ) : ℤ :=
  sSup {k : ℤ | ∃ p q : W → ℤ, p ∈ DomZ g ∧ q ∈ DomZ g ∧ k = LInftyNorm (fun v => p v - q v)}

-- ===== Conjugate scaling (§10.4.5) =====

end DiscreteConvex.AlgorithmsC
