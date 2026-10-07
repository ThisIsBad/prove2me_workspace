import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

namespace LogSobolevMC.Entropy

open scoped BigOperators

/-- The relative entropy `Ent_π(μ) = Σ_x μ(x) log(μ(x)/π(x))` of a probability measure `μ`
with respect to `π` (§2.1, p. 701; §2.4, p. 710). Terms with `μ(x) = 0` vanish. -/
noncomputable def relEnt {V : Type*} [Fintype V] (π μ : V → ℝ) : ℝ :=
  ∑ x, μ x * Real.log (μ x / π x)

/-- The entropy `Ent_π(f) = Σ_x f(x) log f(x) π(x)` of a density `f` (§2.1, p. 701). -/
noncomputable def entF {V : Type*} [Fintype V] (π f : V → ℝ) : ℝ :=
  ∑ x, f x * Real.log (f x) * π x

/-- The semigroup acting on measures, `μH_t(y) = Σ_x H_t(x, y) μ(x)` (Theorem 3.6, p. 722). -/
noncomputable def measHeat {V : Type*} [Fintype V] [DecidableEq V] (K : Matrix V V ℝ) (t : ℝ)
    (μ : V → ℝ) : V → ℝ :=
  Matrix.vecMul μ (MarkovMixing.heatKernel K t)

end LogSobolevMC.Entropy
