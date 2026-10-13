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

/-- Proposition 3.5 (p. 709): a priori estimate. For every dimension `d`, horizon `T` and
Lipschitz constant `L` there is a constant `C`, uniform in the Brownian dimension, such that every square-integrable solution
`(Y, Z, K)` (conditions (v)–(viii) and (v′)) of the RBSDE with data `(ξ, f, S)` satisfying
(i)–(iv) with Lipschitz constant `L` obeys
`E(sup_{0≤t≤T} Y_t² + ∫₀ᵀ |Z_t|² dt + K_T²) ≤ C E(ξ² + ∫₀ᵀ f²(t, 0, 0) dt + sup_{0≤t≤T} (S_t⁺)²)`. -/
theorem proposition_3_5 :
    ∀ (T : ℝ≥0) (L : ℝ), ∃ C : ℝ≥0,
      ∀ (d : ℕ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : IsStdBrownian P B)
        (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
        (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ),
        IsStandardData (augmentedFiltration P hB) P T L ξ f S →
        SatisfiesV (augmentedFiltration P hB) P T Z →
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K →
        SatisfiesVPrime (augmentedFiltration P hB) P T Y K →
        ∫⁻ ω, ((⨆ t ∈ Iic T, ‖Y t ω‖ₑ ^ 2)
            + (∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (euclSq (Z s.toNNReal ω)))
            + ‖K T ω‖ₑ ^ 2) ∂P
          ≤ (C : ℝ≥0∞) * ∫⁻ ω, (‖ξ ω‖ₑ ^ 2
            + (∫⁻ s in Icc (0 : ℝ) T, ‖f s.toNNReal ω 0 0‖ₑ ^ 2)
            + ⨆ t ∈ Iic T, ‖max (S t ω) 0‖ₑ ^ 2) ∂P := by sorry

end ReflectedBSDE.Existence

