import Mathlib
import Definitions.Def_MassartDKW_Binom_Setting

namespace MassartDKW.Binom

/-- Massart (1990), Lemma 1(ii), p. 1272: for `0 < ε ≤ q = 1 − p < 1`,
`h(p, ε) ≥ ε²/[2(p + ε/3)(q − ε/3)] + εφ(t)/t` with `t = ε/(q − ε)`.
For `ε < q` the term `εφ(t)/t` is evaluated at the real number `t = ε/(q − ε)`; at `ε = q`
(`t = ∞`) it takes its limiting value `ε/4` (Lemma 1(i)). -/
theorem lemma_1_ii (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) (hεq : ε ≤ 1 - p) :
    (ε < 1 - p →
      ε ^ 2 / (2 * (p + ε / 3) * (1 - p - ε / 3))
          + ε * phi (ε / (1 - p - ε)) / (ε / (1 - p - ε)) ≤ h p ε) ∧
    (ε = 1 - p →
      ε ^ 2 / (2 * (p + ε / 3) * (1 - p - ε / 3)) + ε / 4 ≤ h p ε) := by sorry

end MassartDKW.Binom

