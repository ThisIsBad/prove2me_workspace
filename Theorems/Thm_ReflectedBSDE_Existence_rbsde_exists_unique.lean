import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Skorohod
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_ReflectedBSDE_Existence_Solution

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Peng1990.SMP

namespace ReflectedBSDE.Existence

/-- Theorem 5.2 (p. 718): under (i)–(iv) and `S_T ≤ ξ`, the RBSDE with (v)–(viii) has a solution
`(Y, Z, K)` (which moreover satisfies (v′)), and any two solutions satisfying (v)–(viii) agree. -/
theorem rbsde_exists_unique {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStdBrownian P B)
    (T : ℝ≥0) (L : ℝ) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hdata : IsStandardData (augmentedFiltration P hB) P T L ξ f S) :
    (∃ (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ),
        SatisfiesV (augmentedFiltration P hB) P T Z ∧
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K ∧
        SatisfiesVPrime (augmentedFiltration P hB) P T Y K) ∧
    ∀ (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
      (Y' : ℝ≥0 → Ω → ℝ) (Z' : ℝ≥0 → Ω → Fin d → ℝ) (K' : ℝ≥0 → Ω → ℝ),
      SatisfiesV (augmentedFiltration P hB) P T Z →
      SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K →
      SatisfiesV (augmentedFiltration P hB) P T Z' →
      SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y' Z' K' →
      SameSolution P T Y Z K Y' Z' K' := by sorry

end ReflectedBSDE.Existence

