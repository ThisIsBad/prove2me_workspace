import Mathlib

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Outward unit normal, expressed by a local C¹ defining function with
negative values precisely on Ω. The positive multiple fixes orientation. -/
def IsOutwardUnitNormal {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (x v : EuclideanSpace ℝ (Fin d)) : Prop :=
  x ∈ frontier Ω ∧ ‖v‖ = 1 ∧
    ∃ V : Set (EuclideanSpace ℝ (Fin d)), IsOpen V ∧ x ∈ V ∧
    ∃ r : EuclideanSpace ℝ (Fin d) → ℝ,
    ∃ scale : ℝ, 0 < scale ∧ ContDiffOn ℝ 1 r V ∧ r x = 0 ∧
      (∀ y ∈ V, y ∈ Ω ↔ r y < 0) ∧
      ∀ h, fderiv ℝ r x h = scale * (∑ i, v i * h i)

end EthierKurtz
