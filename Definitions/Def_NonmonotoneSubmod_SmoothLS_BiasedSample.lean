import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace NonmonotoneSubmod.SmoothLS

variable {X : Type} [Fintype X] [DecidableEq X]

/-- Definition 3.5 (Feige–Mirrokni–Vondrák 2011, p. 1142): the random set `R(A, δ)` sampled with
bias `δ` based on `A` contains each element of `A` independently with probability
`p = (1 + δ)/2` and each element outside `A` independently with probability `q = (1 - δ)/2`.
`biasPt A δ` is the vector of these inclusion probabilities, so that
`E[g(R(A, δ))] = F g (biasPt A δ)`. -/
noncomputable def biasPt (A : Finset X) (δ : ℝ) : X → ℝ :=
  fun i => if i ∈ A then (1 + δ) / 2 else (1 - δ) / 2

/-- The derived potential of Algorithm SLS (p. 1142): `Φ(A) = E[f(R(A, δ))]`. -/
noncomputable def Phi (f : Finset X → ℝ) (δ : ℝ) (A : Finset X) : ℝ :=
  NonmonotoneSubmod.Shared.F f (biasPt A δ)

/-- Step 2 of Algorithm SLS (p. 1142):
`ω_{A,δ}(x) = E[f(R(A, δ) ∪ {x})] - E[f(R(A, δ) \ {x})]`. -/
noncomputable def omegaB (f : Finset X → ℝ) (A : Finset X) (δ : ℝ) (x : X) : ℝ :=
  NonmonotoneSubmod.Shared.F (fun S => f (insert x S)) (biasPt A δ) - NonmonotoneSubmod.Shared.F (fun S => f (S.erase x)) (biasPt A δ)

end NonmonotoneSubmod.SmoothLS
