import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem lemma_3_6 {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0))
    (hf : StrictConvexOn ℝ Set.univ f) (hbdd : BddBelow (Set.range f)) (hργ : ρ * γ < 1) :
    (∃ L : ℝ, Tendsto (fun k => f (Δ k (nextWorst n))) atTop (𝓝 L) ∧
      Tendsto (fun k => f (Δ k (Fin.last n))) atTop (𝓝 L)) ∧
    (2 ≤ n → ∀ N : ℕ, ∃ k ≥ N, Δ (k + 1) (nextWorst n) ≠ Δ k (nextWorst n)) := by sorry

end NelderMeadLD.Dim2

