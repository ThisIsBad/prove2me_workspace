import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_DomZ
import Definitions.Def_DiscreteConvex_AlgorithmsC_L1Norm

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `K̂₁`, Eq. (10.34): the `ℓ¹`-size of `dom g` restricted to pairs sharing a coordinate. -/
noncomputable def Khat1 {W : Type*} [Fintype W] [DecidableEq W] (g : (W → ℤ) → WithTop ℝ) : ℤ :=
  sSup {k : ℤ | ∃ p q : W → ℤ, p ∈ DomZ g ∧ q ∈ DomZ g ∧ (∃ v, p v = q v) ∧
    k = L1Norm (fun v => p v - q v)}

end DiscreteConvex.AlgorithmsC
