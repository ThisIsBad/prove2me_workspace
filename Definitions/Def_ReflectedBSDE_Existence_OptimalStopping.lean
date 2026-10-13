import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ReflectedBSDE.Existence

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `𝒯_t = {v ∈ 𝒯 ; t ≤ v ≤ T}` (p. 705): the `𝓕`-stopping times `v` with `t ≤ v ≤ T`. A
stopping time bounded by `T` is represented by its finite values `v : Ω → [0, ∞[`. -/
def stoppingTimesBetween (𝓕 : Filtration ℝ≥0 mΩ) (t T : ℝ≥0) : Set (Ω → ℝ≥0) :=
  {v | IsStoppingTime 𝓕 (fun ω => (v ω : WithTop ℝ≥0)) ∧ ∀ ω, t ≤ v ω ∧ v ω ≤ T}

/-- `X` is the essential supremum of the family `(F i)_{i ∈ I}` of random variables, relative to
the σ-algebra `m` (the family consists of `m`-measurable variables): `X ≥ F i` almost surely for
every `i`, and `X ≤ W` almost surely for every `m`-measurable `W` with `W ≥ F i` almost surely for
every `i`. -/
def IsEssSupOver {ι : Type*} (P : Measure Ω) (m : MeasurableSpace Ω) (F : ι → Ω → ℝ)
    (X : Ω → ℝ) : Prop :=
  (∀ i, F i ≤ᵐ[P] X) ∧
    ∀ W : Ω → ℝ, StronglyMeasurable[m] W → (∀ i, F i ≤ᵐ[P] W) → X ≤ᵐ[P] W

/-- The reward of stopping at `v` in Proposition 2.3 (p. 705), seen from time `t`:
`∫ₜᵛ f(s, Y_s, Z_s) ds + S_v 1_{v<T} + ξ 1_{v=T}`. -/
noncomputable def stoppingReward {d : ℕ} (T : ℝ≥0) (ξ : Ω → ℝ)
    (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ)
    (Z : ℝ≥0 → Ω → Fin d → ℝ) (t : ℝ≥0) (v : Ω → ℝ≥0) (ω : Ω) : ℝ :=
  (∫ s in Icc (t : ℝ) (v ω), f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω))
    + (if v ω < T then S (v ω) ω else 0) + (if v ω = T then ξ ω else 0)

end ReflectedBSDE.Existence
