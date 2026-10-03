import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions

namespace ProcessingNetworks.Stability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

/-- Proposition 2.2 (SLLN for external arrivals), Dai & Harrison, p. 31: under the baseline
stochastic assumptions, for each buffer `i`, almost surely `E_i(t) / t → λ_i` as `t → ∞`. -/
theorem arrival_process_slln {Ω : Type*} [MeasureSpace Ω] {I J : ℕ} {N0 : Fin J → ℕ}
    {E : Fin I → ℝ → Ω → ℕ} {lam : Fin I → ℝ≥0}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (h : BaselineAssumptions I J N0 E lam v φ m Γ Psi) (i : Fin I) :
    ℙ {ω | Tendsto (fun t : ℝ => (E i t ω : ℝ) / t) atTop (nhds (lam i : ℝ))} = 1 := by sorry

end ProcessingNetworks.Stability
