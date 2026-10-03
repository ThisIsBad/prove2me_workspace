import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_DomZ
import Definitions.Def_DiscreteConvex_AlgorithmsC_L1Norm

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `K₁`, Eq. (10.37): the `ℓ¹`-size of `dom g`. -/
noncomputable def K1 {W : Type*} [Fintype W] [DecidableEq W] (g : (W → ℤ) → WithTop ℝ) : ℤ :=
  sSup {k : ℤ | ∃ p q : W → ℤ, p ∈ DomZ g ∧ q ∈ DomZ g ∧ k = L1Norm (fun v => p v - q v)}

end DiscreteConvex.AlgorithmsC
