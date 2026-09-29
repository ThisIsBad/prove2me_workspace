import Mathlib
import Definitions.Def_FoundationsML_PAC_GeneralizationError
import Definitions.Def_FoundationsML_PAC_EmpiricalError

open MeasureTheory

namespace FoundationsML.PAC

/-- Theorem 2.5 (Learning bound — finite `H`, consistent case; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 15, PDF p. 32).
Let `H` be a finite set of functions mapping from `X` to `Y`. Let `A` be an algorithm that,
for the target concept `c ∈ H`, returns on any i.i.d. sample `S` of size `m` a hypothesis
`A m S ∈ H` consistent with `c` (`R̂_S(A m S) = 0`). Then, for any `ε, δ > 0`, the inequality
`P_{S∼D^m}[R(A m S) ≤ ε] ≥ 1 − δ` holds whenever `m ≥ (1/ε)(log|H| + log(1/δ))`.

**Formalization note.** Carries the book's standing measurability hypothesis (Definition 2.1,
footnote 2, p. 11: "the family of functions `H` and the target concept `c` must be
measurable") on `c` and on every `h ∈ H` — the latter covers `A m S` since `hA_mem` already
places it in `H`. -/
theorem finite_consistent_learning_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (H : Finset (X → Y)) (D : Measure X)
    [IsProbabilityMeasure D] (c : X → Y) (hc : c ∈ H)
    (hc_meas : Measurable c) (hH_meas : ∀ h ∈ H, Measurable h)
    (A : ∀ m : ℕ, (Fin m → X) → (X → Y))
    (hA_mem : ∀ m (S : Fin m → X), A m S ∈ H)
    (hA_consistent : ∀ m (S : Fin m → X), EmpiricalError S c (A m S) = 0)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (m : ℕ) (hm : Real.log (H.card : ℝ) + Real.log (1 / δ) ≤ ε * m) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | GeneralizationError D c (A m S) ≤ ε}).toReal := by sorry

end FoundationsML.PAC
