import Mathlib
import Definitions.Def_FoundationsML_MultiClass_GeneralizationError
import Definitions.Def_FoundationsML_MultiClass_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_MultiClass_Proj1
import Definitions.Def_FoundationsML_MultiClass_RademacherComplexity

open MeasureTheory

namespace FoundationsML.MultiClass

/-- Theorem 9.2 (Margin bound for multi-class classification; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 217, PDF p. 234).
Let `H ⊆ ℝ^{X×Y}` be a hypothesis set with `Y = {1,…,k}` (here `Fin k`, `k ≥ 2`). Fix `ρ > 0`.
Then, for any `δ > 0`, with probability at least `1 − δ`, the following holds for all `h ∈ H`:
`R(h) ≤ R̂_{S,ρ}(h) + (4k/ρ) R_m(Π_1(H)) + sqrt(log(1/δ)/(2m))`.

**Formalization Note.** `hHb`/`hHmeas` guard `RademacherComplexity D (Proj1 H) m` against trap
2, mirroring chunk `03-rademacher-vc`'s `rademacher_generalization_bound` (its own consumer of
this chunk's `EmpiricalRademacherComplexity`/`RademacherComplexity`-shaped definitions), whose
`hGb`/`hGm` guard the same `⨆`/`∫` pattern. Without them, an unbounded `H` collapses
`RademacherComplexity D (Proj1 H) m` to Lean's junk value `0` (real `⨆`/`sSup` of an
unbounded-above set is `0`, not `+∞`), making the theorem's conclusion a small finite quantity
rather than the vacuously-true bound the book's implicit "well-defined complexity" reading
gives — false, not merely unprovable, for such `H`. `hHmeas` states measurability of `Proj1 H`'s
elements directly (`fun x => h (x, y)` for `h ∈ H`, `y : Fin k`), avoiding a need for a
`MeasurableSpace (Fin k)` instance that `RademacherComplexity`'s own signature (over `X`, not
`X × Fin k`) does not otherwise require. -/
theorem margin_bound_multiclass
    {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (k : ℕ) (hk : 2 ≤ k) (f : X → Fin k) (H : Set (X × Fin k → ℝ))
    (hHb : ∃ M : ℝ, ∀ h ∈ H, ∀ z : X × Fin k, |h z| ≤ M)
    (hHmeas : ∀ h ∈ H, ∀ y : Fin k, Measurable (fun x => h (x, y)))
    (m : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D f h ≤
        EmpiricalMarginLoss ρ S f h + (4 * (k : ℝ) / ρ) * RademacherComplexity D (Proj1 H) m +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.MultiClass
