import Mathlib

namespace WassersteinDRO.Duality

/-- The Lipschitz modulus of a real-valued function `φ` on `E` with respect to the fixed norm
`‖·‖`, Kuhn et al. 2019, p. 4 (displayed equation just before Theorem 2):

`Lip(φ) = sup_{ξ≠ξ'} |φ(ξ)-φ(ξ')| / ‖ξ-ξ'‖`.

Valued in `ℝ≥0∞` so that a function that fails to be Lipschitz continuous (no finite bound)
is faithfully recorded as `Lip(φ) = ∞`, matching the paper's own remark that Theorem 5 is
"trivially satisfied" when `Lip(ℓ) = ∞`. -/
noncomputable def lipschitzModulus {E : Type*} [NormedAddCommGroup E] (φ : E → ℝ) : ENNReal :=
  ⨆ (x : E) (y : E) (_ : x ≠ y), ENNReal.ofReal (|φ x - φ y| / ‖x - y‖)

end WassersteinDRO.Duality
