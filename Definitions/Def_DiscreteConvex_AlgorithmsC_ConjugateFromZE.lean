import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_ToEReal

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f(x) = sup{⟨p,x⟩ - g(p) | p ∈ Zⱽ}`, `EReal`-valued, Eq. (10.76). -/
noncomputable def ConjugateFromZE (g : (V → ℤ) → WithTop ℝ) (x : V → ℝ) : EReal :=
  sSup {v : EReal | ∃ p : V → ℤ,
    v = ((∑ i, (p i : ℝ) * x i : ℝ) : EReal) - ToEReal (g p)}

end DiscreteConvex.AlgorithmsC
