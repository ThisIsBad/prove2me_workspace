import Mathlib
open Matrix

namespace PhiDivRobust.Counterpart

/-- The conjugate of the scaled function `λφ` (Ben-Tal et al. 2013, p. 347, proof of Theorem 1):
`(λφ)*(s) = sup_{t ≥ 0} {s t − λ φ(t)}`, valued in `EReal`. With `EReal`'s `0 * ⊤ = 0`,
`(0φ)*(s) = sup_{t ≥ 0} s t`. -/
noncomputable def scaledConj (φ : ℝ → EReal) (lam s : ℝ) : EReal :=
  ⨆ t ∈ Set.Ici (0 : ℝ), ((s * t : ℝ) : EReal) - (lam : EReal) * φ t

end PhiDivRobust.Counterpart
