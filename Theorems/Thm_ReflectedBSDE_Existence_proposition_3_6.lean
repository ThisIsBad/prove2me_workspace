import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Skorohod
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_ReflectedBSDE_Existence_Solution

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Peng1990.SMP

namespace ReflectedBSDE.Existence

universe u

/-- Proposition 3.6 (p. 711): stability. For every `T` and Lipschitz constant `L` there is
a constant `c`, uniform in the Brownian dimension, such that for two data triples `(ξ, f, S)`, `(ξ', f', S')` satisfying (i)–(iv)
with Lipschitz constant `L` and square-integrable solutions `(Y, Z, K)`, `(Y', Z', K')`,
`E(sup|ΔY_t|² + ∫₀ᵀ|ΔZ_t|² dt + |ΔK_T|²) ≤ c E(|Δξ|² + ∫₀ᵀ|Δf(t, Y_t, Z_t)|² dt)
  + c [E(sup|ΔS_t|²)]^{1/2} Ψ_T^{1/2}`. -/
theorem proposition_3_6 :
    ∀ (T : ℝ≥0) (L : ℝ), ∃ c : ℝ≥0,
      ∀ (d : ℕ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : IsStdBrownian P B)
        (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
        (ξ' : Ω → ℝ) (f' : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S' : ℝ≥0 → Ω → ℝ)
        (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
        (Y' : ℝ≥0 → Ω → ℝ) (Z' : ℝ≥0 → Ω → Fin d → ℝ) (K' : ℝ≥0 → Ω → ℝ),
        IsStandardData (augmentedFiltration P hB) P T L ξ f S →
        IsStandardData (augmentedFiltration P hB) P T L ξ' f' S' →
        SatisfiesV (augmentedFiltration P hB) P T Z →
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K →
        SatisfiesVPrime (augmentedFiltration P hB) P T Y K →
        SatisfiesV (augmentedFiltration P hB) P T Z' →
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ' f' S' Y' Z' K' →
        SatisfiesVPrime (augmentedFiltration P hB) P T Y' K' →
        ∫⁻ ω, ((⨆ t ∈ Iic T, ‖Y t ω - Y' t ω‖ₑ ^ 2)
            + (∫⁻ s in Icc (0 : ℝ) T,
                ENNReal.ofReal (euclSq (Z s.toNNReal ω - Z' s.toNNReal ω)))
            + ‖K T ω - K' T ω‖ₑ ^ 2) ∂P
          ≤ (c : ℝ≥0∞) * ∫⁻ ω, (‖ξ ω - ξ' ω‖ₑ ^ 2
              + ∫⁻ s in Icc (0 : ℝ) T,
                ‖f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω)
                  - f' s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω)‖ₑ ^ 2) ∂P
            + (c : ℝ≥0∞) * (supSqMoment P T (fun t ω => S t ω - S' t ω)) ^ (1 / 2 : ℝ)
              * (∫⁻ ω, (‖ξ ω‖ₑ ^ 2
                  + (∫⁻ s in Icc (0 : ℝ) T, ‖f s.toNNReal ω 0 0‖ₑ ^ 2)
                  + (⨆ t ∈ Iic T, ‖max (S t ω) 0‖ₑ ^ 2)
                  + ‖ξ' ω‖ₑ ^ 2
                  + (∫⁻ s in Icc (0 : ℝ) T, ‖f' s.toNNReal ω 0 0‖ₑ ^ 2)
                  + ⨆ t ∈ Iic T, ‖max (S' t ω) 0‖ₑ ^ 2) ∂P) ^ (1 / 2 : ℝ) := by sorry

end ReflectedBSDE.Existence

