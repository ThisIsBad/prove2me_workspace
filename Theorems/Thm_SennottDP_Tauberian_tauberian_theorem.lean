import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), p. 282, Theorem A.4.2. Let `u_n ∈ [0, ∞]` with `u_0 < ∞`, `U(α) = ∑ α^n u_n`
(A.20) and `w_n = ∑_{k=0}^{n-1} u_k`. Then (A.28)
`lim inf_n w_n/n ≤ lim inf_{α→1⁻} (1−α)U(α) ≤ lim sup_{α→1⁻} (1−α)U(α) ≤ lim sup_n w_n/n`,
and the following are equivalent: (i) all the terms in (A.28) are equal and finite;
(ii) `lim_n w_n/n` exists and is finite; (iii) `lim_{α→1⁻} (1−α)U(α)` exists and is finite. -/
theorem tauberian_theorem (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) :
    (liminf (cesaroMean u) atTop ≤ liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
      liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
      limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (cesaroMean u) atTop) ∧
    List.TFAE
      [liminf (cesaroMean u) atTop = liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
          liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) = limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
          limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) = limsup (cesaroMean u) atTop ∧
          limsup (cesaroMean u) atTop ≠ ⊤,
        ∃ L : ℝ≥0∞, L ≠ ⊤ ∧ Tendsto (cesaroMean u) atTop (𝓝 L),
        ∃ L : ℝ≥0∞, L ≠ ⊤ ∧ Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)] := by sorry

end SennottDP.Tauberian
