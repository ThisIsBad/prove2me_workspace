import Mathlib
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Stationarity
open MeasureTheory Filter

namespace KingmanSubadditive.StationaryIncrements

/-- **Theorem 3** (p. 888, §1.4) — Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798.

"Let `Γ(t)` (`t > 0`) be any positive increasing function. Then there exists a process
`(y_t; t ≥ 0)` with stationary increments and finite expectations, whose sample functions have
derivatives of all orders, such that
(1.4.4) `P{|y_t| ≤ Γ(t) for all sufficiently large t} = 0`."

**Formalization Note.** The quantifier order is `∀ Γ, ∃ (Ω, P, y)`. "Increasing" is read as
non-decreasing (`MonotoneOn Γ (Set.Ioi 0)`, the weaker hypothesis); `Γ` is a total function on
`ℝ` whose values at `t ≤ 0` are irrelevant. The process is `y : ℝ → Ω → ℝ`, used for `t ≥ 0`;
each `y_t` is measurable. Stationary increments: `HasStationaryIncrements` (joint laws of the
increment processes on `[0, ∞)`, product σ-algebra). Finite expectations: each `y_t`
(`t ≥ 0`) is integrable. Derivatives of all orders: every sample path is `C^∞` on `[0, ∞)`
(order `((⊤ : ℕ∞) : WithTop ℕ∞)`, smooth; not analytic). In (1.4.4), "for all sufficiently large
`t`" ranges over **real** `t` (`∀ᶠ t in atTop` on `ℝ`); the event need not be measurable a
priori, and `P` of it is its outer measure. -/
theorem theorem_3 (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ y : ℝ → Ω → ℝ,
        (∀ t : ℝ, 0 ≤ t → Measurable (y t)) ∧
        HasStationaryIncrements P y ∧
        (∀ t : ℝ, 0 ≤ t → Integrable (y t) P) ∧
        (∀ ω : Ω, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => y t ω) (Set.Ici 0)) ∧
        P {ω | ∀ᶠ t in atTop, |y t ω| ≤ Γ t} = 0 := by sorry

end KingmanSubadditive.StationaryIncrements

