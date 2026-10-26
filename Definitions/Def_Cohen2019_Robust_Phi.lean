import Mathlib

namespace Cohen2019.Robust

open MeasureTheory ProbabilityTheory

/-- The standard Gaussian CDF `Φ(t) = ℙ(Z ≤ t)`, `Z ∼ 𝒩(0, 1)`.
Cohen, Rosenfeld, Kolter, *Certified Adversarial Robustness via Randomized Smoothing*,
arXiv:1902.02918v2, §3.1, p. 4 ("Φ⁻¹ is the inverse of the standard Gaussian CDF"); used in
(13)–(15), p. 14, and Appendix A.0.1, pp. 15–16 (PDF pages).

**Formalization Note.** `Φ` is Mathlib's `cdf` of `gaussianReal 0 1`. -/
noncomputable def Phi (t : ℝ) : ℝ := cdf (gaussianReal 0 1) t

/-- The real inverse of `Φ` on `(0, 1)`: `Φ⁻¹(p) = inf {t ∈ ℝ : p ≤ Φ(t)}`.
Cohen–Rosenfeld–Kolter, arXiv:1902.02918v2, §3.1, p. 4; Appendix A, pp. 14–16.

**Formalization Note.** For `0 < p < 1` the set is nonempty and bounded below, `Φ` is continuous
and strictly increasing, and `PhiInvReal p` is the unique `t` with `Φ(t) = p`. Outside `(0, 1)`
the value is a Lean junk value (`sInf ∅ = 0` for `p > 1`, `sInf` of a set unbounded below `= 0`
for `p ≤ 0`, and `0` for `p = 1` as well, since `{t | 1 ≤ Φ t} = ∅`); every statement using
`PhiInvReal` assumes `0 < p < 1`. The endpoint values `Φ⁻¹(0) = −∞`, `Φ⁻¹(1) = +∞` are
carried by `PhiInv`. -/
noncomputable def PhiInvReal (p : ℝ) : ℝ := sInf {t : ℝ | p ≤ Phi t}

/-- The extended-real inverse of `Φ` on `[0, 1]`: `Φ⁻¹(p) = −∞` for `p ≤ 0`, `+∞` for `p ≥ 1`,
and `PhiInvReal p` for `0 < p < 1`. Cohen–Rosenfeld–Kolter, arXiv:1902.02918v2, §3.1, p. 4,
eq. (3) and its restatement (7), p. 13 (PDF pages).

**Formalization Note.** The paper evaluates `Φ⁻¹` at the endpoints `p̲A = 1` or `p̄B = 0`, where the
certified radius is `+∞` (p. 4, "R goes to ∞ as p̲A → 1 and p̄B → 0"). Taking values in `EReal`
makes these endpoints the limits `±∞` instead of a junk real `0`. -/
noncomputable def PhiInv (p : ℝ) : EReal :=
  if p ≤ 0 then ⊥ else if 1 ≤ p then ⊤ else ((PhiInvReal p : ℝ) : EReal)

end Cohen2019.Robust
