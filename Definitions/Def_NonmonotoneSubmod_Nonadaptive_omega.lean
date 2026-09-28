import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace NonmonotoneSubmod.Nonadaptive

/-- Definition 2.4 (Feige–Mirrokni–Vondrák 2011, p. 1138): with `R = X(1/2)` a uniformly random
subset of `X`, `ω(x) = E[f(R ∪ {x}) − f(R \ {x})]`. The expectation is the uniform average
`F (fun S => f (S ∪ {x}) - f (S \ {x})) (fun _ => 1/2)` over all subsets `S ⊆ X`. -/
noncomputable def omega {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (x : X) : ℝ :=
  NonmonotoneSubmod.Shared.F (fun S => f (insert x S) - f (S.erase x)) (fun _ => 1 / 2)

end NonmonotoneSubmod.Nonadaptive
