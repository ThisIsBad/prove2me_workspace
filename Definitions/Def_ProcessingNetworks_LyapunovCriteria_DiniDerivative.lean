import Mathlib

namespace ProcessingNetworks.LyapunovCriteria

/-- The upper-right Dini derivative `D⁺f(t)`, Appendix A.4, Eq. (A.9) — restated inline since the
appendices are out of series scope: `D⁺f(t) := limsup_{h ↓ 0} (f(t+h) - f(t))/h`, taken in the
extended reals `EReal` so that the values `+∞` and `-∞` (which the Dini derivative of a merely
continuous function can take) are represented as such rather than by a junk real value. -/
noncomputable def diniUpperRight (f : ℝ → ℝ) (t : ℝ) : EReal :=
  Filter.limsup (fun h : ℝ => (((f (t + h) - f t) / h : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

end ProcessingNetworks.LyapunovCriteria
