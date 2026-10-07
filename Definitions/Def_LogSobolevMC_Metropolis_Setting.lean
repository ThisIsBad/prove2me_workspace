import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_mm_spectral
import Definitions.Def_LogSobolevMC_ChiSquare_Setting
import Definitions.Def_LogSobolevMC_Entropy_Setting

namespace LogSobolevMC.Metropolis

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The smallest eigenvalue `β_min` of a reversible chain (§2.2, p. 702), in its
variational (Rayleigh quotient) form `β_min = inf {⟨Kf, f⟩ / ⟨f, f⟩ : f ≠ 0}`,
with `⟨f, g⟩ = ∑ₓ f(x) g(x) π(x)`. -/
def betaMin (K : Matrix V V ℝ) (π : V → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ f : V → ℝ, f ≠ 0 ∧
    r = MarkovMixing.innerPi π (K.mulVec f) f / MarkovMixing.innerPi π f f}

end

end LogSobolevMC.Metropolis
