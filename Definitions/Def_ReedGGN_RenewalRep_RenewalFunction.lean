import Mathlib

namespace ReedGGN.RenewalRep

open MeasureTheory

/-- Convolution powers of a measure on `ℝ`: `μ^{∗0} = δ₀` and `μ^{∗(n+1)} = μ^{∗n} ∗ μ`
(additive convolution of measures). For the law `μ` of an i.i.d. sequence `η₁, η₂, …`,
`μ^{∗n}` is the law of `S_n = η₁ + ⋯ + η_n`. -/
noncomputable def convPow (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => (convPow μ n).conv μ

/-- The renewal measure `dM = ∑_{n ≥ 1} μ^{∗n}` of the pure renewal process with interarrival
law `μ` (p. 29). Its value on `(-∞, t]` is `∑_{n≥1} P(S_n ≤ t)`, the expected number of renewals
by time `t` (Tonelli). It may be `∞` on a set; it is finite on bounded sets when `μ` is
carried by `[0, ∞)` with `μ {0} < 1`. An atom of `μ` at `0` gives `dM` an atom at `0`. -/
noncomputable def renewalMeasure (μ : Measure ℝ) : Measure ℝ :=
  Measure.sum (fun n : ℕ => convPow μ (n + 1))

/-- The renewal function `M(t) = dM((-∞, t])`, the expected number of renewals by time `t`
(p. 29), as a real number. `toReal` returns `0` if the value is `∞`; statements that need
finiteness state it separately. -/
noncomputable def renewalFn (μ : Measure ℝ) (t : ℝ) : ℝ :=
  (renewalMeasure μ (Set.Iic t)).toReal

end ReedGGN.RenewalRep
