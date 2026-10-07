import Mathlib

/-!
# Lemma 2.2.1: the ergodic lemma behind Loynes' theorem (§2.2.3, p.87)
-/

namespace PalmQueueing.Loynes

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lemma 2.2.1** (p.87). Let `Z` be non-negative, `P⁰`-a.s. finite, and such that
`Z − Z ∘ θ ∈ L¹(P⁰)`. Then `E⁰[Z − Z ∘ θ] = 0`.

The lemma is what makes the uniqueness half of Loynes' theorem work: applied to the difference of
two stationary solutions it forces that difference to be constant, and the flow's ergodicity then
forces it to be zero. The book's own proof is three lines — for any `C > 0`,
`|Z ∧ C − (Z ∧ C) ∘ θ| ≤ |Z − Z ∘ θ|`, and the conclusion follows from
`E⁰[Z ∧ C − (Z ∧ C) ∘ θ] = 0` and dominated convergence.

`Z` is `ℝ`-valued, so "`P⁰`-a.s. finite" is carried by the type. The hypothesis that matters and is
not automatic is the `θ`-invariance of `P⁰`, which Chapter 1's Eq. (1.2.16) supplies. -/
theorem ergodic_lemma (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (shift : Ω → Ω) (hshift : Measurable shift) (hinv : Measure.map shift P0 = P0)
    (Z : Ω → ℝ) (hZmeas : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hint : Integrable (fun ω => Z ω - Z (shift ω)) P0) :
    ∫ ω, (Z ω - Z (shift ω)) ∂P0 = 0 := by sorry

end PalmQueueing.Loynes

