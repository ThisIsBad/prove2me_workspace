import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance

namespace DualSSD.MeanRisk

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The first quantile function `F_X^(−1)(p) = inf {η : F_X(η) ≥ p}`, the left-continuous inverse
of the distribution function (Ogryczak–Ruszczyński 2002, §3, p. 64), for `0 < p ≤ 1`.
Lean's real `sInf` returns `0` on a set that is empty or unbounded below. For `0 < p < 1` the set
is nonempty and bounded below, so the value is the genuine infimum. At `p = 1` the paper's value
is `+∞ ∈ ℝ̄` when `X` is unbounded above, while this definition returns `0`; that single point
does not affect the integral (3.2). No statement of this mission uses `leftQuantile P X 1`
pointwise, and values for `p ≤ 0` or `p > 1` are junk and never used. -/
noncomputable def leftQuantile (P : Measure Ω) (X : Ω → ℝ) (p : ℝ) : ℝ :=
  sInf {η : ℝ | p ≤ Shared.distFun P X η}

/-- `q` is a `p`-quantile of `X` (Ogryczak–Ruszczyński 2002, §3, p. 64):
`P{X < q} ≤ p ≤ P{X ≤ q}`. The paper uses this for `p ∈ [0, 1]`. -/
def IsPQuantile (P : Measure Ω) (X : Ω → ℝ) (p q : ℝ) : Prop :=
  P.real {ω | X ω < q} ≤ p ∧ p ≤ P.real {ω | X ω ≤ q}

/-- The second quantile function (absolute Lorenz curve) (3.2) on `[0, 1]`
(Ogryczak–Ruszczyński 2002, §3, p. 65): `F_X^(−2)(p) = ∫_0^p F_X^(−1)(α) dα` for `0 < p ≤ 1`, and
`F_X^(−2)(0) = 0` (the interval integral over `(0, 0]` is `0`).
The paper's `F_X^(−2)` is `ℝ̄`-valued on all of `ℝ`, with value `+∞` off `[0, 1]`; this mission only
evaluates it on `[0, 1]`, where it is finite when `E|X| < ∞`, so this real-valued version is used.
Its values for `p ∉ [0, 1]` are not the paper's and are never used by any statement. -/
noncomputable def secondQuantileR (P : Measure Ω) (X : Ω → ℝ) (p : ℝ) : ℝ :=
  ∫ α in (0 : ℝ)..p, leftQuantile P X α

end DualSSD.MeanRisk
