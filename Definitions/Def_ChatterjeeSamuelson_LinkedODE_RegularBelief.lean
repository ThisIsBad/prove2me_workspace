import Mathlib

open MeasureTheory ProbabilityTheory Set

namespace ChatterjeeSamuelson.LinkedODE

/-- A player's belief about the opponent's reservation price (Chatterjee & Samuelson,
*Bargaining under Incomplete Information*, Oper. Res. 31(5) 1983, §1, pp. 837–838
[PDF 3–4], unnumbered text: "the buyer regards v_s as a random variable possessing a
cumulative distribution function F_b(v_s) satisfying F_b(v̲_s) = 0 and F_b(v̄_s) = 1, and
which is strictly increasing and differentiable on [v̲_s, v̄_s]"; the seller's `F_s` on
`[v̲_b, v̄_b]` likewise).

`RegularBelief μ lo hi f` says: `μ` is a probability measure on `ℝ` whose distribution
function `F = cdf μ` satisfies `F lo = 0`, `F hi = 1`, is strictly increasing on
`[lo, hi]`, and has derivative `f v` (within `[lo, hi]`) at every `v ∈ [lo, hi]`; the
value interval is nondegenerate, `lo < hi`.

*Formalization Note.* The belief is a measure rather than a bare function so that
expected profits are integrals against it. `cdf μ lo = 0` also rules out an atom at `lo`.
`f` is the paper's density (`f_b`, `f_s`); it is pinned down on `[lo, hi]` only
(one-sided derivatives at the endpoints). `lo < hi` is implicit in the paper's
"strictly increasing on [v̲, v̄]" with `F(v̲) = 0 < 1 = F(v̄)`. -/
def RegularBelief (μ : Measure ℝ) (lo hi : ℝ) (f : ℝ → ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ lo < hi ∧ cdf μ lo = 0 ∧ cdf μ hi = 1 ∧
    StrictMonoOn (cdf μ) (Icc lo hi) ∧
    ∀ v ∈ Icc lo hi, HasDerivWithinAt (cdf μ) (f v) (Icc lo hi) v

end ChatterjeeSamuelson.LinkedODE
