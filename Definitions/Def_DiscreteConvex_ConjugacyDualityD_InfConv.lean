import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The integer infimal convolution `(g1□g2)(p) = inf{g1(p1)+g2(p2) : p1+p2=p}`. -/
noncomputable def InfConv (g1 g2 : (V → ℤ) → WithTop ℝ) (p : V → ℤ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ L = g1 p1 + g2 p2}

end DiscreteConvex.ConjugacyDualityD
