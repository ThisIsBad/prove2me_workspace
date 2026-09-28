import Mathlib

open MeasureTheory

namespace HighDimStat.Concentration

/-- **Eqs. (3.1)-(3.2)**, Wainwright, *High-Dimensional Statistics* (2019), p. 59. The
`φ`-entropy of a nonnegative random variable `Z`, for `φ(u) := u log u` (`u>0`), `φ(0):=0`:

`H(Z) := E[Z log Z] - E[Z] log E[Z]`.

**Formalization Note** `φ(0)=0` holds automatically in Lean, since `Real.log 0 = 0` by
Mathlib's convention, so `Z * Real.log Z = 0` at `Z=0` without needing a case split. -/
noncomputable def phiEntropy {Ω : Type*} [MeasurableSpace Ω] (Z : Ω → ℝ) (Prob : Measure Ω) : ℝ :=
  (∫ ω, Z ω * Real.log (Z ω) ∂Prob) - (∫ ω, Z ω ∂Prob) * Real.log (∫ ω, Z ω ∂Prob)

end HighDimStat.Concentration
