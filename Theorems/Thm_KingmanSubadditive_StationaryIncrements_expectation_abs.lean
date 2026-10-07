import Mathlib
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Stationarity
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Construction
open MeasureTheory ProbabilityTheory Filter

namespace KingmanSubadditive.StationaryIncrements

/-- **Proof of Theorem 3, p. 888 (unnumbered; §1.4)** — Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798.

"Moreover, `E(|y_t|) = E(y₀) = ∫₀¹ E(Y_s) ds = E ∫₀¹ ν₀ψ(ν₀s) ds = E ∫₀^{ν₀} ψ(u) du
= ∫₀¹ ψ(u) du < ∞`."

For the construction of the proof of Theorem 3 (`IsBump ψ`, `IsConstruction Γ P η ν`), every
`y_t` (`t ≥ 0`) is integrable, and
`E(|y_t|) = E(y_0) = ∫₀¹ ψ(u) du`.

**Formalization Note.** Integrability is stated explicitly, so the Bochner integrals are not the
junk value `0` of a non-integrable function. Finiteness of `∫₀¹ ψ` is automatic in `ℝ`. -/
theorem expectation_abs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ)
    (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    ∀ t : ℝ, 0 ≤ t →
      Integrable (procY ψ η ν t) P ∧
        ∫ ω, |procY ψ η ν t ω| ∂P = ∫ ω, procY ψ η ν 0 ω ∂P ∧
        ∫ ω, procY ψ η ν 0 ω ∂P = ∫ u in (0 : ℝ)..1, ψ u := by sorry

end KingmanSubadditive.StationaryIncrements

