import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Witness

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Corollary 2, p. 443, for every witness of Theorem 2 (`r_L = 𝔼[χ_1^{*,L}]`); the chain
`OPT(L) ≥ A ≥ B` is stated as `A ≤ OPT(L)` and `B ≤ A`. -/
theorem corollary2 (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ)
    (hw : IsStationaryWitness P μ κ L₀ L χ q I D)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal ((1 - α) / (1 - α ^ L)) *
          ∑ k ∈ Finset.range L, ENNReal.ofReal (α ^ k) *
            ∫⁻ ω, ENNReal.ofReal
              (G κ (I ω + qN L₀ L q ω 0 - ∑ i ∈ Finset.range (L₀ + 1), D i ω)) ∂P
      ≤ OPT μ κ L₀ L ∧
    ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal (1 - α) *
          ∑ k ∈ Finset.range (L - L₀), ENNReal.ofReal (α ^ k) *
            ∫⁻ ω, ENNReal.ofReal (G κ (I ω
                + ∑ i ∈ Finset.range k, (qN L₀ L q ω i + chiN L₀ L χ ω i - D i ω)
                + qN L₀ L q ω k - ∑ i ∈ Finset.range (L₀ + 1), D (k + i) ω)) ∂P
      ≤ ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal ((1 - α) / (1 - α ^ L)) *
          ∑ k ∈ Finset.range L, ENNReal.ofReal (α ^ k) *
            ∫⁻ ω, ENNReal.ofReal
              (G κ (I ω + qN L₀ L q ω 0 - ∑ i ∈ Finset.range (L₀ + 1), D i ω)) ∂P := by sorry

end XinGoldbergTBS.Asymptotic
