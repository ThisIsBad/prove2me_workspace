import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- `L` is a **Nemitski loss** (Definition 2.16, p. 30, restated locally per Hard Rule 9): there
exist a nonnegative function `b : X → ℝ → [0,∞)` and a nonnegative, increasing function
`h : [0,∞) → [0,∞)` with `L(x,y,t) ≤ b(x,y) + h(|t|)` for all `x, y, t`. -/
def NemitskiLoss {X : Type*} (L : Loss X) : Prop :=
  ∃ (b : X → ℝ → ℝ) (h : ℝ → ℝ),
    (∀ x y, 0 ≤ b x y) ∧ (∀ t, 0 ≤ h t) ∧ Monotone h ∧
      ∀ x y t, L x y t ≤ b x y + h (|t|)

/-- `L` is a **`P`-integrable Nemitski loss** (Definition 2.16, p. 30) for a measure `P` on
`X × ℝ`: `L` is a Nemitski loss with witnesses `b, h` such that `b` (composed with the
projections) is `P`-integrable. -/
def PIntegrableNemitskiLoss {X : Type*} [MeasurableSpace X] (L : Loss X) (P : Measure (X × ℝ)) :
    Prop :=
  ∃ (b : X → ℝ → ℝ) (h : ℝ → ℝ),
    (∀ x y, 0 ≤ b x y) ∧ (∀ t, 0 ≤ h t) ∧ Monotone h ∧
      (∀ x y t, L x y t ≤ b x y + h (|t|)) ∧ Integrable (fun p : X × ℝ => b p.1 p.2) P

end SupportVectorMachines.InfiniteSample
