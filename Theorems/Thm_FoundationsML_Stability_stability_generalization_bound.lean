import Mathlib
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_UniformlyStable

open MeasureTheory

namespace FoundationsML.Stability

/-- Theorem 14.2 (stability-based generalization guarantee; Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 334, PDF p. 351). Assume the
loss function `L` is bounded by `M ≥ 0` for the hypotheses `A` returns. Let `A` be a `β`-stable
learning algorithm and `S` a sample of `m` points drawn i.i.d. from `D`. Then, for any `δ > 0`,
with probability at least `1 − δ`,
`R(h_S) ≤ R̂_S(h_S) + β + (2mβ + M) sqrt(log(1/δ)/(2m))`.

**Formalization Note.** `hbound` is the book's own weaker condition ("for the results
presented in this chapter, a weaker condition suffices, namely that `L_z(h_S) ≤ M` for all
hypotheses `h_S` returned by `A`"), not the stronger `∀ h ∈ H, ∀ z, L_z(h) ≤ M`.

**Revision (2026-09-19).** Added `hAmeas : ∀ S, Measurable (Loss L (A S))`, guarding
`GeneralizationError`'s Bochner integral against trap 2: `GeneralizationError D L (A S)` sits on
the *left* of the load-bearing inequality inside the "good sample" event, so a non-measurable
`Loss L (A S)` for some `S` (nothing in `hstab`/`hbound`, both pointwise algebraic conditions,
constrains `A`'s measurability) would junk the integral to `0`, making that `S` vacuously
satisfy the inequality regardless of whether the book's actual claim holds — the same guard
chunk `03-rademacher-vc`'s `rademacher_generalization_bound` and chunk `05-svm`'s goal already
carry for the identical reason. -/
theorem stability_generalization_bound
    {X Y Y' : Type*} [MeasurableSpace (X × Y)] (D : Measure (X × Y)) [IsProbabilityMeasure D]
    {m : ℕ} (hm : 0 < m)
    (L : Y' → Y → ℝ) (A : (Fin m → X × Y) → (X → Y')) (β M : ℝ)
    (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hstab : UniformlyStable L A β)
    (hbound : ∀ S : Fin m → X × Y, ∀ z : X × Y, Loss L (A S) z ≤ M)
    (hAmeas : ∀ S : Fin m → X × Y, Measurable (Loss L (A S)))
    (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × Y | GeneralizationError D L (A S) ≤
        EmpiricalError L S (A S) + β +
          (2 * m * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.Stability
