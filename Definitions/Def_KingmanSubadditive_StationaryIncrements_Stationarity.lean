import Mathlib

open MeasureTheory

namespace KingmanSubadditive.StationaryIncrements

/-- **Stationary process** on the half-line `t ≥ 0` (the notion used, without definition, in the
proof of Theorem 3, Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973),
DOI 10.1214/aop/1176996798, §1.4, p. 888).

A real-time process `y : ℝ → Ω → ℝ` is *stationary* under `P` if each `y t` (`t ≥ 0`) is a random
variable and, for every `τ ≥ 0`, the shifted process `(y_{t+τ})_{t ≥ 0}` has the same joint law
as `(y_t)_{t ≥ 0}`.

**Formalization Note.** The joint law is the push-forward of `P` under the path map
`Ω → (Set.Ici 0 → ℝ)`, with the product σ-algebra on the path space (so equality of laws is
equality of all finite-dimensional distributions). The measurability clause is part of the
definition, so that `Measure.map` never takes its junk value `0` on a non-measurable path map.
Values `y t` for `t < 0` play no role. -/
def IsStationary {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (y : ℝ → Ω → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → AEMeasurable (y t) P) ∧
  ∀ τ : ℝ, 0 ≤ τ →
    P.map (fun ω (t : Set.Ici (0 : ℝ)) => y ((t : ℝ) + τ) ω) =
      P.map (fun ω (t : Set.Ici (0 : ℝ)) => y (t : ℝ) ω)

/-- **Process with stationary increments** on the half-line `t ≥ 0` (Kingman 1973, §1.4,
pp. 888, Theorem 3; the paper uses the standard notion without defining it).

A real-time process `y : ℝ → Ω → ℝ` has *stationary increments* under `P` if each `y t`
(`t ≥ 0`) is a random variable and, for every `τ ≥ 0`, the increment process
`(y_{t+τ} − y_τ)_{t ≥ 0}` has the same joint law as `(y_t − y_0)_{t ≥ 0}`.

**Formalization Note.** Joint laws are push-forwards of `P` under path maps
`Ω → (Set.Ici 0 → ℝ)` with the product σ-algebra; the measurability clause rules out the junk
value `Measure.map f P = 0` for a non-measurable `f`. Values `y t` for `t < 0` play no role. -/
def HasStationaryIncrements {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (y : ℝ → Ω → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → AEMeasurable (y t) P) ∧
  ∀ τ : ℝ, 0 ≤ τ →
    P.map (fun ω (t : Set.Ici (0 : ℝ)) => y ((t : ℝ) + τ) ω - y τ ω) =
      P.map (fun ω (t : Set.Ici (0 : ℝ)) => y (t : ℝ) ω - y 0 ω)

end KingmanSubadditive.StationaryIncrements
