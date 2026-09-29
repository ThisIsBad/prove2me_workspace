import Mathlib
open Matrix

namespace PhiDivRobust.Counterpart

/-- The conjugate of a φ-divergence function (Ben-Tal et al. 2013, p. 344, Eq. (4)):
`φ*(s) = sup_{t ≥ 0} {s t − φ(t)}`, valued in `EReal`. The supremum runs over `t ≥ 0` only. -/
noncomputable def conj (φ : ℝ → EReal) (s : ℝ) : EReal :=
  ⨆ t ∈ Set.Ici (0 : ℝ), ((s * t : ℝ) : EReal) - φ t

end PhiDivRobust.Counterpart
