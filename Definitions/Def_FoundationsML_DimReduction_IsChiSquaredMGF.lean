import Mathlib

open MeasureTheory

namespace FoundationsML.DimReduction

/-- A real-valued random variable `Q` follows a chi-squared distribution with `k` degrees of
freedom, expressed through its moment-generating function (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition C.7 (appendix) and
Eq. (C.25), cited in the proof of Lemma 15.2, p. 354, PDF p. 371): for all `λ < 1/2`,
`E[exp(λQ)] = (1 − 2λ)^{−k/2}`.

**Formalization Note.** Definition C.7 itself is in the book's appendix, out of this chapter's
page range; the chi-squared distribution's characterizing property actually used by the proof
of Lemma 15.2 — its moment-generating function, Eq. (C.25) — is what this definition states
directly, rather than restating the (unread) appendix definition. `(1 - 2λ)^{-k/2}` uses
`Real.rpow` since the exponent `-k/2` is a real number. -/
noncomputable def IsChiSquaredMGF {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω)
    (Q : Ω → ℝ) (k : ℕ) : Prop :=
  ∀ lam : ℝ, lam < 1 / 2 → ∫ ω, Real.exp (lam * Q ω) ∂Prob = (1 - 2 * lam) ^ (-(k : ℝ) / 2)

end FoundationsML.DimReduction
