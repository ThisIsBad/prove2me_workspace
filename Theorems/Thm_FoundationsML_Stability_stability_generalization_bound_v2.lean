import Mathlib
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_UniformlyStable

open MeasureTheory


namespace FoundationsML.Stability

/-- Theorem 14.2 (stability-based generalization guarantee; goal; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 334, PDF p. 351).
Assume the (non-negative) loss function `L` is bounded by `M ≥ 0` for the hypotheses `A`
returns. Let `A` be a `β`-stable learning algorithm and `S` a sample of `m ≥ 1` points drawn
i.i.d. from `D`. Then, for any `δ ∈ (0,1)`, with probability at least `1 − δ`,
`R(h_S) ≤ R̂_S(h_S) + β + (2mβ + M) sqrt(log(1/δ)/(2m))`.

**Formalization Note.** Replaces `stability_generalization_bound`, which bounded the loss only
from above (`L_z(h_S) ≤ M`) and so admitted negative losses, for which the bound is false (the
disproof used a loss in `{−1, 0}`). The chapter's standing convention `L : Y' × Y → ℝ_+`
(p. 333) is now explicit (`hLnn`), so that `L_z(h_S) ∈ [0, M]` as McDiarmid's step requires.
`hbound` remains the book's weaker condition ("`L_z(h_S) ≤ M` for all hypotheses `h_S`
returned by `A`"). The standing measurability convention is stated as joint measurability of
`(S, z) ↦ L_z(h_S)` (`hAmeas`; it yields the measurability of each `z ↦ L_z(h_S)` assumed
before, and of `S ↦ R(h_S)` to which McDiarmid's inequality is applied). `δ < 1` is the
standing convention for a confidence level. -/
theorem stability_generalization_bound_v2
    {X Y Y' : Type*} [MeasurableSpace (X × Y)] (D : Measure (X × Y)) [IsProbabilityMeasure D]
    {m : ℕ} (hm : 0 < m)
    (L : Y' → Y → ℝ) (hLnn : ∀ y' y, 0 ≤ L y' y)
    (A : (Fin m → X × Y) → (X → Y')) (β M : ℝ)
    (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hstab : UniformlyStable L A β)
    (hbound : ∀ S : Fin m → X × Y, ∀ z : X × Y, Loss L (A S) z ≤ M)
    (hAmeas : Measurable (fun p : (Fin m → X × Y) × (X × Y) => Loss L (A p.1) p.2))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × Y | GeneralizationError D L (A S) ≤
        EmpiricalError L S (A S) + β +
          (2 * m * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.Stability

