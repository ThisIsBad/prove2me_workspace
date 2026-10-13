import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ToEReal

namespace DiscreteConvex.ConjugacyDualityC

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The integer infimal convolution `(g1□g2)(p) = inf{g1(p1)+g2(p2) : p1+p2=p}` computed in
`EReal`, where the infimum is genuine. `InfConv` takes the same infimum in `WithTop ℝ`, which is
only conditionally complete: when the values are unbounded below it reads the junk value `0`
(`g1(p) = p₁` and `g2(p) = -p₁ + p₂` are L-convex with `g1 □ g2 = -∞` everywhere, and `InfConv`
returns the constant `0`). Murota's L₂-convex functions require `g1 □ g2 > -∞`, which is
`InfConvE g1 g2 p ≠ ⊥`. -/
noncomputable def InfConvE (g1 g2 : (V → ℤ) → WithTop ℝ) (p : V → ℤ) : EReal :=
  sInf {L : EReal | ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ L = ToEReal (g1 p1) + ToEReal (g2 p2)}

end DiscreteConvex.ConjugacyDualityC
