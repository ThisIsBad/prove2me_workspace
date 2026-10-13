import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Skorohod
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_ReflectedBSDE_Existence_Solution

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Peng1990.SMP

namespace ReflectedBSDE.Existence

/-- Proposition 2.2 (p. 705): for a solution of (vi)–(viii), almost surely, for every
`t ∈ [0, T]`,
`K_T − K_t = sup_{t≤u≤T} (ξ + ∫ᵤᵀ f(s, Y_s, Z_s) ds − ∫ᵤᵀ (Z_s, dB_s) − S_u)⁻`,
where `∫ᵤᵀ (Z_s, dB_s) = Σⱼ (Jʲ_T − Jʲ_u)` for the stochastic integrals `J` of the solution. -/
theorem proposition_2_2 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStdBrownian P B)
    (T : ℝ≥0) (L : ℝ) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hdata : IsStandardData (augmentedFiltration P hB) P T L ξ f S)
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
    (J : Fin d → ℝ≥0 → Ω → ℝ)
    (hsol : SolvesRBSDEWith (augmentedFiltration P hB) P T B ξ f S Y Z K J) :
    ∀ᵐ ω ∂P, ∀ t ≤ T,
      K T ω - K t ω = ⨆ u : Icc t T,
        max (-(ξ ω
          + (∫ s in Icc ((u : ℝ≥0) : ℝ) T, f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω))
          - ∑ j, (J j T ω - J j u ω) - S u ω)) 0 := by sorry

end ReflectedBSDE.Existence

