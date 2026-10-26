import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem lemma_3_1 {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0)) :
    (∀ k, Nondegenerate (Δ k)) ∧
    (∀ k, ¬ IsShrinkAt f ρ χ γ Δ k →
      vol (Δ (k + 1)) = |tau ρ χ γ (move f ρ χ γ (Δ k))| * vol (Δ k)) ∧
    (∀ k, IsShrinkAt f ρ χ γ Δ k → vol (Δ (k + 1)) = σ ^ n * vol (Δ k)) := by sorry

end NelderMeadLD.Dim2

