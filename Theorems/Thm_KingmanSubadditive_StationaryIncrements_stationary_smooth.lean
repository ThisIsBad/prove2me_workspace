import Mathlib
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Stationarity
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Construction
open MeasureTheory ProbabilityTheory Filter

namespace KingmanSubadditive.StationaryIncrements

/-- **Proof of Theorem 3, p. 888 (unnumbered; §1.4)** — Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798.

"Then `(y_t)` is clearly stationary, and therefore has stationary increments, and its sample
functions are of class `C^∞`."

Let `Γ` be positive and increasing on `(0, ∞)`, `ψ` the bump function of the proof (`IsBump`),
and `η, ν₀, ν₁, …` independent, `η` uniform on `(0, 1)`, each `ν_r` with law `m_Γ`
(`IsConstruction`). Then the process `y_t = Y_{t+η}` of (1.4.5) is stationary, has stationary
increments, and every sample path `t ↦ y_t(ω)` is `C^∞` on `[0, ∞)`.

**Formalization Note.** `C^∞` is the order `((⊤ : ℕ∞) : WithTop ℕ∞)` (smooth), not
`⊤ : WithTop ℕ∞` (analytic). Smoothness is claimed for every `ω`, not almost every. -/
theorem stationary_smooth {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ)
    (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    IsStationary P (procY ψ η ν) ∧ HasStationaryIncrements P (procY ψ η ν) ∧
      ∀ ω : Ω, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => procY ψ η ν t ω) (Set.Ici 0) := by sorry

end KingmanSubadditive.StationaryIncrements

