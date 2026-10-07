import Mathlib

namespace MassartDKW.Binom

/-- Massart (1990), Lemma 1, p. 1272: `φ(t) = t − t²/(2(1 + 2t/3)) − log(1 + t)`, for `t ≥ 0`. -/
noncomputable def phi (t : ℝ) : ℝ :=
  t - t ^ 2 / (2 * (1 + 2 * t / 3)) - Real.log (1 + t)

/-- Massart (1990), Lemma 1, p. 1272: with `q = 1 − p`,
`h(p, ε) = (p + ε) log((p + ε)/p) + (q − ε) log((q − ε)/q)`.
It is meaningful for `0 < ε ≤ q = 1 − p < 1`; at `ε = q` the second term is `0 · log 0 = 0`. -/
noncomputable def h (p ε : ℝ) : ℝ :=
  (p + ε) * Real.log ((p + ε) / p) + (1 - p - ε) * Real.log ((1 - p - ε) / (1 - p))

end MassartDKW.Binom
