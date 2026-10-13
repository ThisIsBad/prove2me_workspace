import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Skorohod
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_ReflectedBSDE_Existence_Solution
import Definitions.Def_ReflectedBSDE_Existence_OptimalStopping

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Peng1990.SMP

namespace ReflectedBSDE.Existence

/-- Proposition 2.3 (p. 705): for a solution of (v)–(viii) (hence of (v′)), and with the obstacle
in `𝒮²` (Remark 3.2), for each `t ∈ [0, T]`,
`Y_t = ess sup_{v ∈ 𝒯_t} E[∫ₜᵛ f(s, Y_s, Z_s) ds + S_v 1_{v<T} + ξ 1_{v=T} | 𝓕_t]`. -/
theorem proposition_2_3 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStdBrownian P B)
    (T : ℝ≥0) (L : ℝ) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hdata : IsStandardData (augmentedFiltration P hB) P T L ξ f S)
    (hS2 : IsS2 (augmentedFiltration P hB) P T S)
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
    (hZ : SatisfiesV (augmentedFiltration P hB) P T Z)
    (hsol : SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K)
    (hYK : SatisfiesVPrime (augmentedFiltration P hB) P T Y K) :
    ∀ t ≤ T, IsEssSupOver P (augmentedFiltration P hB t)
      (fun v : stoppingTimesBetween (augmentedFiltration P hB) t T =>
        condExp (augmentedFiltration P hB t) P (stoppingReward T ξ f S Y Z t v))
      (Y t) := by sorry

end ReflectedBSDE.Existence

