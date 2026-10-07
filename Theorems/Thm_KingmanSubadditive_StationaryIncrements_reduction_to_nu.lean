import Mathlib
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Stationarity
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Construction
open MeasureTheory ProbabilityTheory Filter

namespace KingmanSubadditive.StationaryIncrements

/-- **Proof of Theorem 3, p. 889 (unnumbered; §1.4)** — Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798.

"`P{|y_t| ≤ Γ(t) for all sufficiently large t}
≤ P{|y(n + ½ν_n⁻¹ − η)| ≤ Γ(n + ½ν_n⁻¹ − η) for all sufficiently large n}
≤ P{ν_n ≤ Γ(n + ½) for all sufficiently large n} = 0`."

For the construction of the proof of Theorem 3 (`Γ` positive and increasing on `(0, ∞)`,
`IsBump ψ`, `IsConstruction Γ P η ν`), with `t_n = n + ½ν_n⁻¹ − η`:
1. `P{|y_t| ≤ Γ(t) for all large real t} ≤ P{|y(t_n)| ≤ Γ(t_n) for all large n}`;
2. `P{|y(t_n)| ≤ Γ(t_n) for all large n} ≤ P{ν_n ≤ Γ(n + ½) for all large n}`;
3. `P{ν_n ≤ Γ(n + ½) for all large n} = 0`.

**Formalization Note.** "For all sufficiently large `t`" is `∀ᶠ t in atTop` over the reals,
"for all sufficiently large `n`" is `∀ᶠ n in atTop` over `ℕ`. These events need not be
measurable a priori; `P` of a set is its outer measure. `ν_n⁻¹` is the real inverse (`ν_n ≥ 1`
almost surely). -/
theorem reduction_to_nu {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ)
    (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    P {ω | ∀ᶠ t in atTop, |procY ψ η ν t ω| ≤ Γ t}
        ≤ P {ω | ∀ᶠ n : ℕ in atTop,
            |procY ψ η ν ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) ω|
              ≤ Γ ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω)} ∧
      P {ω | ∀ᶠ n : ℕ in atTop,
            |procY ψ η ν ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) ω|
              ≤ Γ ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω)}
        ≤ P {ω | ∀ᶠ n : ℕ in atTop, (ν n ω : ℝ) ≤ Γ ((n : ℝ) + 1 / 2)} ∧
      P {ω | ∀ᶠ n : ℕ in atTop, (ν n ω : ℝ) ≤ Γ ((n : ℝ) + 1 / 2)} = 0 := by sorry

end KingmanSubadditive.StationaryIncrements

