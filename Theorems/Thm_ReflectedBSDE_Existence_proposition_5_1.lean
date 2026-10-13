import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Skorohod
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_ReflectedBSDE_Existence_Solution

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Peng1990.SMP

namespace ReflectedBSDE.Existence

/-- Proposition 5.1 (p. 716): if the coefficient `f(t)` does not depend on `(y, z)` and is a
progressively measurable process with (ii′) `E ∫₀ᵀ f(t)² dt < ∞`, then under (i), (iv) and
`S_T ≤ ξ` the backward reflection problem (v), (vi′), (vii), (viii) has a unique solution. -/
theorem proposition_5_1 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStdBrownian P B)
    (T : ℝ≥0) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hξ : IsTerminalValue (augmentedFiltration P hB) P T ξ)
    (hf : L2F (augmentedFiltration P hB) P T f)
    (hS : IsObstacle (augmentedFiltration P hB) P T S)
    (hST : ∀ᵐ ω ∂P, S T ω ≤ ξ ω) :
    (∃ (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ),
        SatisfiesV (augmentedFiltration P hB) P T Z ∧
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ (fun t ω _ _ => f t ω) S Y Z K) ∧
    ∀ (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
      (Y' : ℝ≥0 → Ω → ℝ) (Z' : ℝ≥0 → Ω → Fin d → ℝ) (K' : ℝ≥0 → Ω → ℝ),
      SatisfiesV (augmentedFiltration P hB) P T Z →
      SolvesRBSDE (augmentedFiltration P hB) P T B ξ (fun t ω _ _ => f t ω) S Y Z K →
      SatisfiesV (augmentedFiltration P hB) P T Z' →
      SolvesRBSDE (augmentedFiltration P hB) P T B ξ (fun t ω _ _ => f t ω) S Y' Z' K' →
      SameSolution P T Y Z K Y' Z' K' := by sorry

end ReflectedBSDE.Existence

