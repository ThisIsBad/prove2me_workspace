import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_conj
open Matrix

namespace PhiDivRobust.Counterpart

/-- The term `λ φ*(s/λ)` of the robust counterpart (13) (Ben-Tal et al. 2013, p. 347, Theorem 1),
with the paper's convention for `λ = 0`: `0 φ*(s/0) := 0` if `s ≤ 0` and `:= +∞` if `s > 0`.
Only `λ ≥ 0` is ever used; the `else` branch is the `λ = 0` convention. -/
noncomputable def perspConj (φ : ℝ → EReal) (lam s : ℝ) : EReal :=
  if 0 < lam then (lam : EReal) * conj φ (s / lam) else if s ≤ 0 then 0 else ⊤

end PhiDivRobust.Counterpart
