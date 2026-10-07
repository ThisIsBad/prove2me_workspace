import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_LogSobolevMC_ChiSquare_Setting
import Definitions.Def_LogSobolevMC_Entropy_Setting

namespace LogSobolevMC.TwoPoint

open MarkovMixing
open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The chain `K(x, y) = π(y)` of the Appendix (p. 742): every step is an independent draw from `π`. -/
def indepChain (π : V → ℝ) : Matrix V V ℝ :=
  fun _ y => π y

/-- `π_* = min_𝒳 π` (Theorem A.1, p. 742). -/
def piMin [Nonempty V] (π : V → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty π

/-- The kernel `K(x, y) = 1/(|𝒳| − 1)` for `x ≠ y`, `K(x, x) = 0` of Corollary A.5 (p. 747):
the simple random walk on the complete graph on `𝒳`. -/
def completeChain (V : Type*) [Fintype V] [DecidableEq V] : Matrix V V ℝ :=
  fun x y => if x = y then 0 else 1 / ((Fintype.card V : ℝ) - 1)

end

/-- The chain on `{0, 1}` with matrix `( θ 1 − θ ; θ 1 − θ )` of Theorem A.2 (p. 743). -/
noncomputable def twoPointChain (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![θ, 1 - θ; θ, 1 - θ]

/-- The measure `π(0) = θ`, `π(1) = 1 − θ` on `{0, 1}` (Theorem A.2, p. 743). -/
noncomputable def twoPointPi (θ : ℝ) : Fin 2 → ℝ :=
  ![θ, 1 - θ]

/-- The function `l(s)` of the proof of Theorem A.2 (p. 743): `ℒ` of the function with values
`x = 1 + (1 − θ)s`, `y = 1 − θs` under `π = (θ, 1 − θ)`. -/
noncomputable def lFun (θ s : ℝ) : ℝ :=
  θ * (1 + (1 - θ) * s) ^ 2 * Real.log ((1 + (1 - θ) * s) ^ 2)
    + (1 - θ) * (1 - θ * s) ^ 2 * Real.log ((1 - θ * s) ^ 2)
    - (1 + θ * (1 - θ) * s ^ 2) * Real.log (1 + θ * (1 - θ) * s ^ 2)

/-- The function `e(s) = θ(1 − θ)s²` of the proof of Theorem A.2 (p. 744): `ℰ` of the same function. -/
noncomputable def eFun (θ s : ℝ) : ℝ :=
  θ * (1 - θ) * s ^ 2

end LogSobolevMC.TwoPoint
